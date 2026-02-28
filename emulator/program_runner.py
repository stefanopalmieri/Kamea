"""
program_runner — Sequential statement execution for .ds programs.

Wraps EmulatorHost to manage env bindings, statement sequencing,
and step-by-step control for the debugger.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from emulator.ds_loader import (
    load_ds_file, parse_expression, classify_statement,
    ast_to_term, RawWord,
)
from emulator.host import EmulatorHost
from emulator.machine import S_FETCH, S_DONE, S_HALTED


# ---------------------------------------------------------------------------
# Statement representation
# ---------------------------------------------------------------------------

@dataclass
class Statement:
    kind: str           # "def", "print", "if", "expr"
    node: object        # original AST node
    source_text: str    # for display
    args: tuple         # kind-specific payload


def _node_to_source(node) -> str:
    """Best-effort source text from an AST node."""
    return repr(node) if node is not None else ""


# ---------------------------------------------------------------------------
# ProgramRunner
# ---------------------------------------------------------------------------

class ProgramRunner:
    """Manages sequential evaluation of statements from a .ds program."""

    def __init__(self, backend: str = "rom", **host_kwargs):
        self.host = EmulatorHost(backend=backend, **host_kwargs)
        self.machine = self.host.machine
        self.env: dict[str, RawWord] = {}
        self.output_lines: list[str] = []
        self.statements: list[Statement] = []
        self.current_stmt_idx: int = 0
        self.phase: str = "idle"  # "idle" | "running" | "between" | "done"

        # Multi-phase state for print/if
        self._print_parts: list[str] = []
        self._print_args: list = []
        self._print_arg_idx: int = 0
        self._if_phase: str = ""  # "cond" | "branch"
        self._if_cond_node = None
        self._if_then_node = None
        self._if_else_node = None
        self._def_name: str = ""

    # -------------------------------------------------------------------
    # Loading
    # -------------------------------------------------------------------

    def load_file(self, path: str | Path):
        """Parse a .ds file and prepare statements."""
        nodes = load_ds_file(path)
        self._classify_nodes(nodes)

    def load_expression(self, text: str):
        """Parse expression text and prepare statements."""
        nodes = parse_expression(text)
        self._classify_nodes(nodes)

    def _classify_nodes(self, nodes: list):
        """Convert AST nodes into Statement objects."""
        for node in nodes:
            classified = classify_statement(node)
            kind = classified[0]
            source = _node_to_source(node)

            if kind == "def":
                _, name, expr = classified
                self.statements.append(Statement(
                    kind="def", node=node, source_text=source,
                    args=(name, expr),
                ))
            elif kind == "print":
                _, print_args = classified
                self.statements.append(Statement(
                    kind="print", node=node, source_text=source,
                    args=(print_args,),
                ))
            elif kind == "if":
                _, cond, then_n, else_n = classified
                self.statements.append(Statement(
                    kind="if", node=node, source_text=source,
                    args=(cond, then_n, else_n),
                ))
            else:  # "expr"
                _, expr_node = classified
                self.statements.append(Statement(
                    kind="expr", node=node, source_text=source,
                    args=(expr_node,),
                ))

    # -------------------------------------------------------------------
    # Execution control
    # -------------------------------------------------------------------

    def _load_term_with_env(self, term) -> int:
        """Load a term that may contain RawWord values into the heap.

        RawWord values are wrapped in QUOTE to prevent re-evaluation.
        Other terms go through host.load_term(). Tuples are handled recursively.
        """
        if isinstance(term, RawWord):
            # All tags except TAG_APP self-evaluate in S_DECODE.
            # TAG_APP words would be re-evaluated as function applications,
            # so we rebuild them using the (APP f x) constructor which
            # produces a proper data pair via the machine's dispatch.
            from emulator.machine import TAG_APP, unpack_word
            tag = (term.word >> 60) & 0xF
            if tag == TAG_APP:
                _, f_addr, x_addr, _ = unpack_word(term.word)
                f_word = self.machine.heap_read(f_addr)
                x_word = self.machine.heap_read(x_addr)
                # Build ((APP f) x) which evaluates to the APP data pair
                app_atom_addr = self.host.load_term("APP")
                f_val_addr = self.machine.alloc(f_word)
                x_val_addr = self.machine.alloc(x_word)
                from emulator.machine import make_app_word
                inner_app = make_app_word(app_atom_addr, f_val_addr)
                inner_addr = self.machine.alloc(inner_app)
                outer_app = make_app_word(inner_addr, x_val_addr)
                return self.machine.alloc(outer_app)
            return self.machine.alloc(term.word)

        if isinstance(term, tuple):
            if len(term) == 2:
                if term[0] == "QUOTED":
                    inner_addr = self._load_term_with_env(term[1])
                    from emulator.machine import make_quoted_word
                    word = make_quoted_word(inner_addr)
                    return self.machine.alloc(word)
                else:
                    f_addr = self._load_term_with_env(term[0])
                    x_addr = self._load_term_with_env(term[1])
                    from emulator.machine import make_app_word
                    word = make_app_word(f_addr, x_addr)
                    return self.machine.alloc(word)

        # Plain str or int — delegate to host.load_term
        return self.host.load_term(term)

    def _load_and_start(self, term):
        """Reset SP and state (NOT heap), load term, set S_FETCH."""
        self.machine.sp.load(0)
        self.machine.state.load(S_FETCH)
        self.machine.reset_counters()

        addr = self._load_term_with_env(term)

        self.machine.tp.load(addr)
        self.machine.state.load(S_FETCH)

    def begin_next_statement(self) -> bool:
        """Set up the machine for the next statement.

        Returns False if all statements are done.
        """
        if self.current_stmt_idx >= len(self.statements):
            self.phase = "done"
            return False

        stmt = self.statements[self.current_stmt_idx]

        if stmt.kind == "def":
            name, expr = stmt.args
            self._def_name = name
            term = ast_to_term(expr, self.env)
            self._load_and_start(term)
            self.phase = "running"

        elif stmt.kind == "print":
            (print_args,) = stmt.args
            self._print_args = print_args
            self._print_arg_idx = 0
            self._print_parts = []
            self._begin_next_print_arg()

        elif stmt.kind == "if":
            cond, then_n, else_n = stmt.args
            self._if_phase = "cond"
            self._if_then_node = then_n
            self._if_else_node = else_n
            term = ast_to_term(cond, self.env)
            self._load_and_start(term)
            self.phase = "running"

        elif stmt.kind == "expr":
            (expr_node,) = stmt.args
            term = ast_to_term(expr_node, self.env)
            self._load_and_start(term)
            self.phase = "running"

        return True

    def _begin_next_print_arg(self):
        """Start evaluating the next print argument."""
        while self._print_arg_idx < len(self._print_args):
            tag, arg = self._print_args[self._print_arg_idx]
            if tag == "string":
                # String literal — display directly, no machine eval needed
                self._print_parts.append(arg)
                self._print_arg_idx += 1
                continue
            else:
                # Expression — needs machine evaluation
                term = ast_to_term(arg, self.env)
                self._load_and_start(term)
                self.phase = "running"
                return

        # All print args done
        line = " ".join(self._print_parts)
        self.output_lines.append(line)
        self._advance_statement()

    def _advance_statement(self):
        """Move to the next statement."""
        self.current_stmt_idx += 1
        self.phase = "between"

    def on_eval_complete(self):
        """Called when the machine reaches S_DONE. Handle the result."""
        result_word = self.machine.result.value
        stmt = self.statements[self.current_stmt_idx]

        if stmt.kind == "def":
            self.env[self._def_name] = RawWord(result_word)
            self._advance_statement()

        elif stmt.kind == "print":
            decoded = self.host.decode_word(result_word)
            self._print_parts.append(decoded)
            self._print_arg_idx += 1
            self._begin_next_print_arg()

        elif stmt.kind == "if":
            if self._if_phase == "cond":
                # Check if result is ⊤
                decoded = self.host.decode_word(result_word)
                if decoded == "⊤":
                    branch_node = self._if_then_node
                else:
                    branch_node = self._if_else_node
                self._if_phase = "branch"
                term = ast_to_term(branch_node, self.env)
                self._load_and_start(term)
                self.phase = "running"
            else:
                # Branch phase done
                self._advance_statement()

        elif stmt.kind == "expr":
            self._advance_statement()

    # -------------------------------------------------------------------
    # Tick interface
    # -------------------------------------------------------------------

    def tick(self) -> bool:
        """Advance the machine one cycle.

        If idle/between, begin the next statement.
        If the machine halts, call on_eval_complete().
        Returns False when all statements are done.
        """
        if self.phase == "done":
            return False

        if self.phase in ("idle", "between"):
            if not self.begin_next_statement():
                return False
            # If begin_next_statement set phase to "between" (e.g. string-only print),
            # recurse to start the next one
            if self.phase == "between":
                return self.tick()
            # If still not running (all done), return
            if self.phase != "running":
                return False

        # Phase is "running" — tick the machine
        state = self.machine.state.value
        if state in (S_DONE, S_HALTED):
            self.on_eval_complete()
            # May have started a new eval (multi-phase print/if)
            if self.phase == "done":
                return False
            if self.phase == "between":
                return True  # caller should tick again to start next stmt
            return True

        self.machine.tick()

        # Check if machine just completed
        state = self.machine.state.value
        if state in (S_DONE, S_HALTED):
            self.on_eval_complete()
            if self.phase == "done":
                return False

        return True
