use wasm_bindgen::prelude::*;
use serde::Serialize;

use psi_core::eval::{Evaluator, EvalConfig, StepResult};
use psi_core::table::{self, NAMES};
use psi_core::term::Term;
use psi_runtime::io::BufferIo;
use psi_runtime::machine::{Machine, Value, VOID_TERM};

#[wasm_bindgen]
pub struct PsiDebugger {
    machine: Machine<BufferIo>,
    /// Current evaluator for stepping (if any).
    evaluator: Option<Evaluator>,
    /// The term being evaluated by the stepper.
    eval_term: Option<u32>,
    /// Trace of evaluation steps.
    trace: Vec<TraceEntry>,
}

#[derive(Clone, Serialize)]
struct TraceEntry {
    step: usize,
    rule: String,
    term_display: String,
}

#[derive(Serialize)]
struct TableData {
    size: usize,
    cells: Vec<Vec<u8>>,
    names: Vec<String>,
    roles: Vec<String>,
}

#[derive(Serialize)]
struct TermNode {
    kind: String,
    value: Option<String>,
    children: Vec<TermNode>,
    int_value: Option<i64>,
    is_list: bool,
    list_items: Vec<TermNode>,
}

#[derive(Serialize)]
struct StepInfo {
    done: bool,
    rule: String,
    term_display: String,
    step_count: usize,
    depth: usize,
}

#[derive(Serialize)]
struct Stats {
    steps: usize,
    arena_size: usize,
    trace_len: usize,
}

#[wasm_bindgen]
impl PsiDebugger {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        PsiDebugger {
            machine: Machine::new(BufferIo::new()),
            evaluator: None,
            eval_term: None,
            trace: Vec::new(),
        }
    }

    /// Load and run a Mini-Lisp source string. Returns output.
    pub fn run(&mut self, source: &str) -> String {
        self.trace.clear();
        self.evaluator = None;
        self.eval_term = None;

        match self.machine.run(source) {
            Ok(results) => {
                let mut output = String::new();
                for r in results {
                    if let Value::Term(t) = r {
                        if t != VOID_TERM {
                            output.push_str(&self.machine.display(t));
                            output.push('\n');
                        }
                    }
                }
                // Append IO output
                let io_out: Vec<u8> = self.machine.io.output.drain(..).collect();
                if !io_out.is_empty() {
                    output.push_str(&String::from_utf8_lossy(&io_out));
                }
                output
            }
            Err(e) => format!("error: {}", e),
        }
    }

    /// Run source and return JSON with both display strings and term trees.
    pub fn run_with_trees(&mut self, source: &str) -> String {
        self.trace.clear();
        self.evaluator = None;
        self.eval_term = None;

        #[derive(Serialize)]
        struct RunResult {
            error: Option<String>,
            results: Vec<ResultEntry>,
            io_output: String,
        }
        #[derive(Serialize)]
        struct ResultEntry {
            display: String,
            tree: TermNode,
        }

        match self.machine.run(source) {
            Ok(results) => {
                let mut entries = Vec::new();
                for r in &results {
                    if let Value::Term(t) = r {
                        if *t != VOID_TERM {
                            entries.push(ResultEntry {
                                display: self.machine.display(*t),
                                tree: self.build_term_node(*t, 50),
                            });
                        }
                    }
                }
                let io_out: Vec<u8> = self.machine.io.output.drain(..).collect();
                let io_str = String::from_utf8_lossy(&io_out).to_string();
                serde_json::to_string(&RunResult {
                    error: None,
                    results: entries,
                    io_output: io_str,
                }).unwrap_or_default()
            }
            Err(e) => {
                serde_json::to_string(&RunResult {
                    error: Some(e.to_string()),
                    results: vec![],
                    io_output: String::new(),
                }).unwrap_or_default()
            }
        }
    }

    /// Evaluate a raw Ψ∗ expression and step through it.
    /// Pass a simple term like "E(Q(3))" — builds the term in the arena
    /// and starts the evaluator for stepping.
    pub fn start_stepping(&mut self, expr: &str) -> String {
        self.trace.clear();

        // Parse simple term expressions
        let term = match self.parse_term_expr(expr) {
            Ok(t) => t,
            Err(e) => return format!("parse error: {}", e),
        };

        self.eval_term = Some(term);
        self.evaluator = Some(Evaluator::new(term));

        let display = self.machine.arena.display_term(term, 30);
        format!("Stepping: {}", display)
    }

    /// Execute one evaluation step. Returns JSON StepInfo.
    pub fn step(&mut self) -> String {
        let evaluator = match self.evaluator.as_mut() {
            Some(e) => e,
            None => return serde_json::to_string(&StepInfo {
                done: true,
                rule: "no evaluator".to_string(),
                term_display: "".to_string(),
                step_count: 0,
                depth: 0,
            }).unwrap_or_default(),
        };

        let config = EvalConfig { max_steps: 1_000_000 };
        let result = evaluator.step(&mut self.machine.arena, &config);

        match result {
            StepResult::Done(r) => {
                let display = self.machine.arena.display_term(r, 30);
                self.trace.push(TraceEntry {
                    step: evaluator.step_count(),
                    rule: "done".to_string(),
                    term_display: display.clone(),
                });
                serde_json::to_string(&StepInfo {
                    done: true,
                    rule: "done".to_string(),
                    term_display: display,
                    step_count: evaluator.step_count(),
                    depth: evaluator.depth(),
                }).unwrap_or_default()
            }
            StepResult::Continue { rule, term } => {
                let display = self.machine.arena.display_term(term, 30);
                self.trace.push(TraceEntry {
                    step: evaluator.step_count(),
                    rule: rule.to_string(),
                    term_display: display.clone(),
                });
                serde_json::to_string(&StepInfo {
                    done: false,
                    rule: rule.to_string(),
                    term_display: display,
                    step_count: evaluator.step_count(),
                    depth: evaluator.depth(),
                }).unwrap_or_default()
            }
            StepResult::Error(e) => {
                serde_json::to_string(&StepInfo {
                    done: true,
                    rule: format!("error: {}", e),
                    term_display: "".to_string(),
                    step_count: evaluator.step_count(),
                    depth: evaluator.depth(),
                }).unwrap_or_default()
            }
        }
    }

    /// Run the current evaluator to completion. Returns result display string.
    pub fn run_to_completion(&mut self) -> String {
        let evaluator = match self.evaluator.as_mut() {
            Some(e) => e,
            None => return "no evaluator active".to_string(),
        };

        let config = EvalConfig { max_steps: 1_000_000 };
        match evaluator.run(&mut self.machine.arena, &config) {
            Ok(r) => self.machine.arena.display_term(r, 30),
            Err(e) => format!("error: {}", e),
        }
    }

    /// Get the Cayley table as JSON.
    pub fn table(&self) -> String {
        let mut cells = Vec::new();
        for row in &table::TABLE {
            cells.push(row.to_vec());
        }
        let names: Vec<String> = NAMES.iter().map(|s| s.to_string()).collect();
        let roles: Vec<String> = (0..16).map(|i| {
            match i {
                0 | 1 => "absorber".to_string(),
                3 => "tester".to_string(),
                2 | 4 => "encoder".to_string(),
                6 | 7 | 8 | 9 | 10 => "operator".to_string(),
                _ => "inert".to_string(),
            }
        }).collect();
        let data = TableData { size: 16, cells, names, roles };
        serde_json::to_string(&data).unwrap_or_default()
    }

    /// Get current term as JSON tree.
    pub fn current_term(&self) -> String {
        if let Some(ref eval) = self.evaluator {
            if let Some(result) = eval.get_result() {
                return self.term_to_json(result);
            }
        }
        if let Some(t) = self.eval_term {
            return self.term_to_json(t);
        }
        "null".to_string()
    }

    /// Get eval trace as JSON.
    pub fn eval_trace(&self) -> String {
        serde_json::to_string(&self.trace).unwrap_or_default()
    }

    /// Write input byte.
    pub fn input(&mut self, byte: u8) {
        self.machine.io.input.push_back(byte);
    }

    /// Read output bytes as string.
    pub fn output(&mut self) -> String {
        let out: Vec<u8> = self.machine.io.output.drain(..).collect();
        String::from_utf8_lossy(&out).to_string()
    }

    /// Get machine stats as JSON.
    pub fn stats(&self) -> String {
        let s = Stats {
            steps: self.evaluator.as_ref().map(|e| e.step_count()).unwrap_or(0),
            arena_size: self.machine.arena.len(),
            trace_len: self.trace.len(),
        };
        serde_json::to_string(&s).unwrap_or_default()
    }

    /// Reset the machine.
    pub fn reset(&mut self) {
        self.machine = Machine::new(BufferIo::new());
        self.evaluator = None;
        self.eval_term = None;
        self.trace.clear();
    }

    // --- Private helpers ---

    /// Parse a simple term expression like "App(E, App(Q, Atom(3)))" or shorthand "E(Q(3))".
    fn parse_term_expr(&mut self, expr: &str) -> Result<u32, String> {
        let expr = expr.trim();

        // Atom by name
        for (i, name) in NAMES.iter().enumerate() {
            if expr == *name {
                return Ok(self.machine.arena.atom(i as u8));
            }
        }

        // Atom by number
        if let Ok(n) = expr.parse::<u8>() {
            if n < 16 {
                return Ok(self.machine.arena.atom(n));
            }
        }

        // Nat shorthand: "nat(5)"
        if expr.starts_with("nat(") && expr.ends_with(')') {
            let inner = &expr[4..expr.len()-1];
            let n: u64 = inner.parse().map_err(|_| "bad nat argument")?;
            return Ok(self.machine.arena.nat(n));
        }

        // App(fun, arg) or shorthand F(A) where F is an atom name
        if let Some(paren_pos) = expr.find('(') {
            if expr.ends_with(')') {
                let prefix = &expr[..paren_pos];
                let inner = &expr[paren_pos+1..expr.len()-1];

                // If prefix is an atom name, it's shorthand for App(atom, ...)
                let fun_idx = NAMES.iter().position(|n| *n == prefix);

                if let Some(atom_idx) = fun_idx {
                    let fun = self.machine.arena.atom(atom_idx as u8);
                    let arg = self.parse_term_expr(inner)?;
                    return Ok(self.machine.arena.app(fun, arg));
                }

                if prefix == "App" {
                    // Split on first comma at top level (respecting parens)
                    let (a, b) = split_at_comma(inner)?;
                    let fun = self.parse_term_expr(a)?;
                    let arg = self.parse_term_expr(b)?;
                    return Ok(self.machine.arena.app(fun, arg));
                }

                if prefix == "Atom" {
                    let n: u8 = inner.parse().map_err(|_| "bad atom index")?;
                    return Ok(self.machine.arena.atom(n));
                }
            }
        }

        Err(format!("cannot parse term: {}", expr))
    }

    fn term_to_json(&self, idx: u32) -> String {
        let node = self.build_term_node(idx, 50);
        serde_json::to_string(&node).unwrap_or_default()
    }

    fn build_term_node(&self, idx: u32, depth: usize) -> TermNode {
        if depth == 0 {
            return TermNode {
                kind: "truncated".to_string(),
                value: Some("...".to_string()),
                children: vec![],
                int_value: None,
                is_list: false,
                list_items: vec![],
            };
        }

        match self.machine.arena.get(idx) {
            Term::Atom(a) => TermNode {
                kind: "atom".to_string(),
                value: Some(NAMES[a as usize].to_string()),
                children: vec![],
                int_value: None,
                is_list: false,
                list_items: vec![],
            },
            Term::App { fun, arg } => {
                // Check for integer
                if let Some(n) = self.machine.arena.decode_int(idx) {
                    return TermNode {
                        kind: "int".to_string(),
                        value: Some(n.to_string()),
                        children: vec![],
                        int_value: Some(n),
                        is_list: false,
                        list_items: vec![],
                    };
                }

                // Check for proper list
                if self.machine.arena.is_proper_list(idx) && self.machine.arena.as_pair(idx).is_some() {
                    let elems = self.machine.arena.list_elements(idx);
                    let items: Vec<TermNode> = elems.iter()
                        .map(|&e| self.build_term_node(e, depth - 1))
                        .collect();
                    return TermNode {
                        kind: "list".to_string(),
                        value: None,
                        children: vec![],
                        int_value: None,
                        is_list: true,
                        list_items: items,
                    };
                }

                // Check for dotted pair
                if let Some((car, cdr)) = self.machine.arena.as_pair(idx) {
                    return TermNode {
                        kind: "pair".to_string(),
                        value: None,
                        children: vec![
                            self.build_term_node(car, depth - 1),
                            self.build_term_node(cdr, depth - 1),
                        ],
                        int_value: None,
                        is_list: false,
                        list_items: vec![],
                    };
                }

                TermNode {
                    kind: "app".to_string(),
                    value: None,
                    children: vec![
                        self.build_term_node(fun, depth - 1),
                        self.build_term_node(arg, depth - 1),
                    ],
                    int_value: None,
                    is_list: false,
                    list_items: vec![],
                }
            }
        }
    }
}

/// Split a string at the top-level comma (respecting nested parentheses).
fn split_at_comma(s: &str) -> Result<(&str, &str), String> {
    let mut depth = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                return Ok((s[..i].trim(), s[i+1..].trim()));
            }
            _ => {}
        }
    }
    Err("no comma found in App arguments".to_string())
}
