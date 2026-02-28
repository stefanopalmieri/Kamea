"""
Textual TUI debugger for the Kamea emulator.

Cycle-stepping debugger that loads .ds programs, runs them on the emulator,
and displays full machine state at every step.

Usage:
    uv run python -m emulator.debugger examples/alu_74181_demo.ds
    uv run python -m emulator.debugger -e "(((:ALU_ARITH :N9) :N3) :N5)"
    uv run python -m emulator.debugger --run examples/alu_74181_demo.ds
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from textual.app import App, ComposeResult
from textual.binding import Binding
from textual.containers import ScrollableContainer
from textual.widgets import Static, RichLog, Footer
from textual import work
from textual.worker import Worker

from emulator.ds_loader import classify_statement, RawWord
from emulator.program_runner import ProgramRunner, Statement
from emulator.machine import (
    S_FETCH, S_DECODE, S_EVAL_R, S_EVAL_R2, S_APPLY, S_DOT,
    S_ALU, S_IO, S_RETURN, S_DONE, S_HALTED,
    unpack_word,
)
from emulator import cayley

STATE_NAMES = {
    S_FETCH: "S_FETCH", S_DECODE: "S_DECODE", S_EVAL_R: "S_EVAL_R",
    S_EVAL_R2: "S_EVAL_R2", S_APPLY: "S_APPLY", S_DOT: "S_DOT",
    S_ALU: "S_ALU", S_IO: "S_IO", S_RETURN: "S_RETURN",
    S_DONE: "S_DONE", S_HALTED: "S_HALTED",
}

def _esc(text: str) -> str:
    """Escape Rich markup characters in text."""
    return text.replace("[", "\\[")


TAG_NAMES = {
    0x0: "ATOM", 0x1: "QUOTE", 0x2: "APP", 0x3: "ALUP1", 0x4: "ALUP2",
    0x5: "IOPUTP", 0x6: "IOSEQP", 0x7: "BUNDLE", 0x8: "PARTIAL",
    0x9: "COUT", 0xA: "W32", 0xB: "W16", 0xC: "WPACK",
    0xD: "W32OP1", 0xE: "MULOP1", 0xF: "EXT",
}


# ---------------------------------------------------------------------------
# CSS
# ---------------------------------------------------------------------------

DEBUGGER_CSS = """
Screen {
    layout: grid;
    grid-size: 2 4;
    grid-columns: 1fr 1fr;
    grid-rows: 1fr 1fr 1fr auto;
}

.panel {
    border: solid $accent;
    border-title-align: left;
    overflow-y: auto;
    height: 100%;
}

#source-panel { column-span: 1; }
#state-panel  { column-span: 1; }
#stack-panel  { column-span: 1; }
#heap-panel   { column-span: 1; }
#io-panel     { column-span: 1; }
#output-panel { column-span: 1; }

Footer {
    column-span: 2;
}
"""


# ---------------------------------------------------------------------------
# Panel widgets
# ---------------------------------------------------------------------------

class SourcePanel(ScrollableContainer):
    """Source code with current statement highlighted."""
    BORDER_TITLE = "Source"

    def compose(self) -> ComposeResult:
        yield Static("", id="source-content")


class StatePanel(ScrollableContainer):
    """Machine state: registers, counters."""
    BORDER_TITLE = "Machine State"

    def compose(self) -> ComposeResult:
        yield Static("", id="state-content")


class StackPanel(ScrollableContainer):
    """Stack contents, top-down."""
    BORDER_TITLE = "Stack"

    def compose(self) -> ComposeResult:
        yield Static("", id="stack-content")


class HeapPanel(ScrollableContainer):
    """Heap contents, top-down from HP."""
    BORDER_TITLE = "Heap"

    def compose(self) -> ComposeResult:
        yield Static("", id="heap-content")


class IOPanel(ScrollableContainer):
    """UART TX/RX FIFO contents."""
    BORDER_TITLE = "IO"

    def compose(self) -> ComposeResult:
        yield Static("", id="io-content")


class OutputPanel(ScrollableContainer):
    """Accumulated program output."""
    BORDER_TITLE = "Output"

    def compose(self) -> ComposeResult:
        yield RichLog(id="output-log", markup=True, wrap=True)


# ---------------------------------------------------------------------------
# Main debugger app
# ---------------------------------------------------------------------------

class KameaDebugger(App):
    """Textual TUI debugger for the Kamea emulator."""

    CSS = DEBUGGER_CSS
    TITLE = "Kamea Debugger"

    BINDINGS = [
        Binding("s", "step_1", "Step"),
        Binding("space", "step_1", "Step", show=False),
        Binding("n", "step_10", "x10"),
        Binding("f", "step_100", "x100"),
        Binding("r", "run_to_end", "Run"),
        Binding("b", "toggle_breakpoint", "Break"),
        Binding("p", "run_to_print", "→Print"),
        Binding("q", "quit", "Quit"),
    ]

    def __init__(self, runner: ProgramRunner, auto_run: bool = False):
        super().__init__()
        self.runner = runner
        self.auto_run = auto_run
        self.breakpoints: set[int] = set()
        self._output_line_count = 0
        self._running_worker: Worker | None = None

    def compose(self) -> ComposeResult:
        yield SourcePanel(id="source-panel", classes="panel")
        yield StatePanel(id="state-panel", classes="panel")
        yield StackPanel(id="stack-panel", classes="panel")
        yield HeapPanel(id="heap-panel", classes="panel")
        yield IOPanel(id="io-panel", classes="panel")
        yield OutputPanel(id="output-panel", classes="panel")
        yield Footer()

    def on_mount(self) -> None:
        self.refresh_panels()
        if self.auto_run:
            self.action_run_to_end()

    # -------------------------------------------------------------------
    # Panel refresh
    # -------------------------------------------------------------------

    def refresh_panels(self) -> None:
        self._refresh_source()
        self._refresh_state()
        self._refresh_stack()
        self._refresh_heap()
        self._refresh_io()
        self._refresh_output()

    def _refresh_source(self) -> None:
        lines = []
        for i, stmt in enumerate(self.runner.statements):
            prefix = "●" if i in self.breakpoints else " "
            marker = "▸" if i == self.runner.current_stmt_idx else " "
            source = stmt.source_text
            if len(source) > 60:
                source = source[:57] + "..."
            line = f"{prefix}{marker} {i:2d}│ {source}"
            if i == self.runner.current_stmt_idx:
                line = f"[bold reverse]{line}[/bold reverse]"
            lines.append(line)

        content = self.query_one("#source-content", Static)
        content.update("\n".join(lines) if lines else "(no program loaded)")

    def _refresh_state(self) -> None:
        m = self.runner.machine
        state_name = STATE_NAMES.get(m.state.value, f"?({m.state.value})")
        result_hex = f"0x{m.result.value:016X}"
        try:
            result_decoded = _esc(self.runner.host.decode_word(m.result.value))
        except Exception:
            result_decoded = "?"

        idx = self.runner.current_stmt_idx
        total = len(self.runner.statements)
        stmt_info = f"{idx}/{total}"
        if idx < total:
            stmt_info += f" ({self.runner.statements[idx].kind})"

        text = (
            f"[bold]State:[/bold] {state_name}    [bold]Cycle:[/bold] {m.cycles}\n"
            f"[bold]TP:[/bold] 0x{m.tp.value:06X}  [bold]HP:[/bold] 0x{m.hp.value:06X}  "
            f"[bold]SP:[/bold] 0x{m.sp.value:04X}\n"
            f"[bold]Result:[/bold] {result_hex}\n"
            f"  → {result_decoded}\n"
            f"[bold]ROM:[/bold] {m.rom_reads}  [bold]ALU:[/bold] {m.alu_ops}  "
            f"[bold]IO:[/bold] {m.io_ops}\n"
            f"[bold]Heap:[/bold] {m.heap_reads}R/{m.heap_writes}W  "
            f"[bold]Stack peak:[/bold] {m.stack_peak}\n"
            f"[bold]Stmt:[/bold] {stmt_info}  [bold]Phase:[/bold] {self.runner.phase}"
        )
        content = self.query_one("#state-content", Static)
        content.update(text)

    def _refresh_stack(self) -> None:
        m = self.runner.machine
        sp = m.sp.value
        lines = []
        for i in range(sp - 1, -1, -1):
            word = m.stack.read(i)
            try:
                decoded = self.runner.host.decode_word(word)
            except Exception:
                decoded = "?"
            # Return states are raw ints pushed for the state machine
            decoded = _esc(decoded)
            if word in (S_EVAL_R, S_APPLY):
                state_label = STATE_NAMES.get(word, "?")
                lines.append(f"\\[{i:3d}] ret→{state_label}")
            else:
                lines.append(f"\\[{i:3d}] {decoded}")
        content = self.query_one("#stack-content", Static)
        content.update("\n".join(lines) if lines else "(empty)")

    def _refresh_heap(self) -> None:
        m = self.runner.machine
        hp = m.hp.value
        tp = m.tp.value
        lines = []
        # Show up to 50 most recent heap entries
        start = max(0, hp - 50)
        for addr in range(hp - 1, start - 1, -1):
            word = m.heap.read(addr)
            tag, left, right, meta = unpack_word(word)
            tag_name = TAG_NAMES.get(tag, f"?{tag}")
            try:
                decoded = self.runner.host.decode_word(word)
            except Exception:
                decoded = "?"
            decoded = _esc(decoded)
            if len(decoded) > 40:
                decoded = decoded[:37] + "..."
            line = f"{addr:04X}: \\[{tag_name:6s}] {decoded}"
            if addr == tp:
                line = f"[green]{line}[/green]"
            lines.append(line)
        content = self.query_one("#heap-content", Static)
        content.update("\n".join(lines) if lines else "(empty)")

    def _refresh_io(self) -> None:
        m = self.runner.machine
        tx_buf = list(m.uart_tx.buffer)
        rx_buf = list(m.uart_rx.buffer)

        def fmt_buf(buf: list[int]) -> str:
            if not buf:
                return "(empty)"
            hex_str = " ".join(f"{b:02X}" for b in buf)
            ascii_str = "".join(chr(b) if 32 <= b < 127 else "." for b in buf)
            return f"{hex_str}  │ {ascii_str}"

        text = (
            f"[bold]TX:[/bold] {fmt_buf(tx_buf)}\n"
            f"[bold]RX:[/bold] {fmt_buf(rx_buf)}"
        )
        content = self.query_one("#io-content", Static)
        content.update(text)

    def _refresh_output(self) -> None:
        log = self.query_one("#output-log", RichLog)
        while self._output_line_count < len(self.runner.output_lines):
            log.write(self.runner.output_lines[self._output_line_count])
            self._output_line_count += 1

    # -------------------------------------------------------------------
    # Actions
    # -------------------------------------------------------------------

    def _report_error(self, err: Exception) -> None:
        """Show an error in the output panel."""
        self.runner.output_lines.append(f"[ERROR] {err}")
        self.runner.phase = "done"
        self.refresh_panels()

    def _do_steps(self, count: int) -> None:
        try:
            for _ in range(count):
                if not self.runner.tick():
                    break
        except Exception as e:
            self._report_error(e)
            return
        self.refresh_panels()

    def action_step_1(self) -> None:
        self._do_steps(1)

    def action_step_10(self) -> None:
        self._do_steps(10)

    def action_step_100(self) -> None:
        self._do_steps(100)

    def action_toggle_breakpoint(self) -> None:
        idx = self.runner.current_stmt_idx
        if idx in self.breakpoints:
            self.breakpoints.discard(idx)
        else:
            self.breakpoints.add(idx)
        self._refresh_source()

    @work(thread=True)
    def action_run_to_end(self) -> None:
        """Run to completion in a background thread."""
        try:
            cycle = 0
            prev_stmt = self.runner.current_stmt_idx
            while self.runner.tick():
                cycle += 1
                # Check breakpoints on statement transitions
                if self.runner.current_stmt_idx != prev_stmt:
                    prev_stmt = self.runner.current_stmt_idx
                    if prev_stmt in self.breakpoints:
                        self.call_from_thread(self.refresh_panels)
                        return
                if cycle % 500 == 0:
                    self.call_from_thread(self.refresh_panels)
        except Exception as e:
            self.call_from_thread(self._report_error, e)
            return
        self.call_from_thread(self.refresh_panels)

    @work(thread=True)
    def action_run_to_print(self) -> None:
        """Run until the next print statement completes."""
        try:
            cycle = 0
            prev_stmt = self.runner.current_stmt_idx
            while self.runner.tick():
                cycle += 1
                curr = self.runner.current_stmt_idx
                # A statement transition happened
                if curr != prev_stmt:
                    # Check if the statement that just completed was a print
                    if prev_stmt < len(self.runner.statements):
                        if self.runner.statements[prev_stmt].kind == "print":
                            self.call_from_thread(self.refresh_panels)
                            return
                    # Check breakpoints
                    if curr in self.breakpoints:
                        self.call_from_thread(self.refresh_panels)
                        return
                    prev_stmt = curr
                if cycle % 500 == 0:
                    self.call_from_thread(self.refresh_panels)
        except Exception as e:
            self.call_from_thread(self._report_error, e)
            return
        self.call_from_thread(self.refresh_panels)


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Kamea emulator TUI debugger",
        prog="python -m emulator.debugger",
    )
    parser.add_argument("file", nargs="?", help="Path to .ds program file")
    parser.add_argument("-e", "--expr", help="Single expression to evaluate")
    parser.add_argument("--run", action="store_true",
                        help="Run to completion immediately (auto-run mode)")
    parser.add_argument("--neural", action="store_true",
                        help="Use neural MLP backend instead of ROM for dot")
    parser.add_argument("--llm", action="store_true",
                        help="Use LLM backend (Ollama) instead of ROM for dot")
    args = parser.parse_args()

    if not args.file and not args.expr:
        parser.error("Provide a .ds file or -e expression")

    if args.llm:
        backend = "llm"
    elif args.neural:
        backend = "neural"
    else:
        backend = "rom"
    runner = ProgramRunner(backend=backend)

    try:
        if args.file:
            path = Path(args.file)
            if not path.exists():
                print(f"Error: File not found: {path}", file=sys.stderr)
                sys.exit(1)
            runner.load_file(path)
        else:
            runner.load_expression(args.expr)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    app = KameaDebugger(runner, auto_run=args.run)
    app.run()


if __name__ == "__main__":
    main()
