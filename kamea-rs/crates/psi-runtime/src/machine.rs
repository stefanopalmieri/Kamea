use psi_core::eval::{self, EvalConfig, EvalError};
use psi_core::table::{BOT, TOP, F_ENC, ETA, TABLE, NAMES, TABLE_C, NAMES_C};
use psi_core::term::{Arena, Term};
use crate::io::IoChannel;
use crate::lisp::{SExpr, Function, Env, parse_all};
use std::collections::HashMap;

/// Machine stats.
#[derive(Clone, Debug, Default)]
pub struct MachineStats {
    pub arena_size: usize,
}

/// A value in the Mini-Lisp environment.
#[derive(Clone, Debug)]
pub enum Value {
    Term(u32),
    Function(Function),
    Builtin(String),
}

/// Sentinel: defun/setq return void, not printed.
pub const VOID_TERM: u32 = u32::MAX;

/// The Ψ∗ machine.
pub struct Machine<I: IoChannel> {
    pub arena: Arena,
    pub io: I,
    pub eval_config: EvalConfig,
    pub env: Env,
    symbol_table: HashMap<String, i64>,
    next_symbol_id: i64,
    /// The Cayley table (Ψ₁₆ᶠ or Ψ₁₆ᶜ).
    table: &'static [[u8; 16]; 16],
    /// Element names matching the active table.
    names: &'static [&'static str; 16],
}

impl<I: IoChannel> Machine<I> {
    /// Create a new machine with the default Ψ₁₆ᶠ table.
    pub fn new(io: I) -> Self {
        Self::with_table(io, &TABLE, &NAMES)
    }

    /// Create a new machine with the Ψ₁₆ᶜ table.
    pub fn new_c(io: I) -> Self {
        Self::with_table(io, &TABLE_C, &NAMES_C)
    }

    /// Create a new machine with a specific Cayley table and names.
    pub fn with_table(io: I, table: &'static [[u8; 16]; 16], names: &'static [&'static str; 16]) -> Self {
        let mut m = Machine {
            arena: Arena::new(1_000_000),
            io,
            eval_config: EvalConfig { max_steps: 1_000_000 },
            env: Env::new(),
            symbol_table: HashMap::new(),
            next_symbol_id: 100,
            table,
            names,
        };
        m.register_builtins();
        m
    }

    fn register_builtins(&mut self) {
        let builtins = [
            "+", "-", "*", "/", "<", ">", "<=", ">=", "=", "eq", "equal",
            "cons", "car", "cdr", "null", "zerop", "atom", "numberp",
            "display", "print", "terpri", "list", "mod", "1+", "1-",
            "write-char", "write-string",
            "dot", "atom-name",
        ];
        for name in builtins {
            self.env.insert(name.to_string(), Value::Builtin(name.to_string()));
        }
    }

    /// Evaluate a Ψ∗ term (psi_eval).
    pub fn psi_eval(&mut self, term: u32) -> Result<u32, EvalError> {
        eval::eval_with_table(&mut self.arena, term, &self.eval_config, self.table)
    }

    /// Encode integer (Mini-Lisp convention: n+1 Q layers).
    pub fn encode_int(&mut self, n: i64) -> u32 {
        self.arena.encode_int(n as u64)
    }

    /// Decode integer (Mini-Lisp convention).
    pub fn decode_int(&self, term: u32) -> Option<i64> {
        self.arena.decode_int(term)
    }

    /// Build a cons pair.
    pub fn cons(&mut self, car: u32, cdr: u32) -> u32 {
        self.arena.pair(car, cdr)
    }

    /// Display a term in Lisp format.
    pub fn display(&self, term: u32) -> String {
        self.arena.display_lisp(term)
    }

    /// Run a source string, return results.
    pub fn run(&mut self, source: &str) -> Result<Vec<Value>, String> {
        let exprs = parse_all(source).map_err(|e| e.to_string())?;
        let mut results = Vec::new();
        for expr in exprs {
            let result = self.evaluate(&expr)?;
            results.push(result);
        }
        Ok(results)
    }

    /// Run and display results (convenience for CLI).
    pub fn run_and_print(&mut self, source: &str) -> Result<(), String> {
        let results = self.run(source)?;
        for r in results {
            match r {
                Value::Term(t) if t != VOID_TERM => {
                    let s = self.display(t);
                    for b in s.bytes() {
                        self.io.put(b);
                    }
                    self.io.put(b'\n');
                    self.io.flush();
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Evaluate an S-expression, returning a Value.
    pub fn evaluate(&mut self, sexpr: &SExpr) -> Result<Value, String> {
        match sexpr {
            SExpr::Int(n) => Ok(Value::Term(self.encode_int(*n))),

            SExpr::Str(s) => {
                let decoded = decode_escape(s);
                let bot = self.arena.atom(BOT);
                let mut result = bot;
                for c in decoded.chars().rev() {
                    let ch = self.encode_int(c as i64);
                    result = self.cons(ch, result);
                }
                Ok(Value::Term(result))
            }

            SExpr::Symbol(name) => {
                if let Some(val) = self.env.get(name) {
                    return Ok(val);
                }
                let up = name.to_uppercase();
                if up == "NIL" {
                    Ok(Value::Term(self.arena.atom(BOT)))
                } else if up == "T" {
                    Ok(Value::Term(self.arena.atom(TOP)))
                } else {
                    Err(format!("unbound variable: {}", name))
                }
            }

            SExpr::List(items) if items.is_empty() => {
                Ok(Value::Term(self.arena.atom(BOT)))
            }

            SExpr::List(items) => self.eval_list(items),
        }
    }

    fn eval_list(&mut self, items: &[SExpr]) -> Result<Value, String> {
        let head = &items[0];

        // Check for special forms
        if let SExpr::Symbol(name) = head {
            match name.as_str() {
                "quote" => {
                    if items.len() != 2 {
                        return Err("quote takes exactly 1 argument".to_string());
                    }
                    let t = self.translate_datum(&items[1])?;
                    return Ok(Value::Term(t));
                }

                "if" => {
                    if items.len() < 3 {
                        return Err("if requires test and then-branch".to_string());
                    }
                    let cond_val = self.eval_to_term(&items[1])?;
                    if self.arena.get(cond_val) == Term::Atom(BOT) {
                        if items.len() >= 4 {
                            return self.evaluate(&items[3]);
                        }
                        return Ok(Value::Term(self.arena.atom(BOT)));
                    }
                    return self.evaluate(&items[2]);
                }

                "cond" => {
                    for clause in &items[1..] {
                        if let SExpr::List(parts) = clause {
                            if parts.len() < 2 {
                                return Err("bad cond clause".to_string());
                            }
                            let cond_val = self.eval_to_term(&parts[0])?;
                            if self.arena.get(cond_val) != Term::Atom(BOT) {
                                return self.evaluate(&parts[1]);
                            }
                        } else {
                            return Err("bad cond clause".to_string());
                        }
                    }
                    return Ok(Value::Term(self.arena.atom(BOT)));
                }

                "defun" => {
                    if items.len() < 4 {
                        return Err("defun requires name, args, body".to_string());
                    }
                    let fname = expect_symbol(&items[1])?;
                    let params = expect_param_list(&items[2])?;
                    let body = if items.len() == 4 {
                        items[3].clone()
                    } else {
                        wrap_progn(&items[3..])
                    };
                    // Closure captures current env by Rc (O(1)).
                    // Self-reference works automatically: the closure
                    // points to the same frame we insert into below.
                    let func = Function {
                        params,
                        body,
                        closure: self.env.clone(),
                        name: Some(fname.clone()),
                    };
                    self.env.insert(fname, Value::Function(func));
                    return Ok(Value::Term(VOID_TERM));
                }

                "setq" => {
                    if items.len() != 3 {
                        return Err("setq requires name and expression".to_string());
                    }
                    let vname = expect_symbol(&items[1])?;
                    let val = self.evaluate(&items[2])?;
                    self.env.insert(vname, val);
                    return Ok(Value::Term(VOID_TERM));
                }

                "define" => {
                    return self.eval_define(items);
                }

                "let" => {
                    if items.len() < 3 {
                        return Err("let requires bindings and body".to_string());
                    }
                    let bindings = if let SExpr::List(bs) = &items[1] {
                        bs
                    } else {
                        return Err("let bindings must be a list".to_string());
                    };
                    let body = if items.len() == 3 {
                        items[2].clone()
                    } else {
                        wrap_progn(&items[2..])
                    };
                    let parent = self.env.clone(); // O(1) Rc clone
                    let saved_env = std::mem::replace(&mut self.env, Env::child(&parent));
                    for binding in bindings {
                        if let SExpr::List(parts) = binding {
                            if parts.len() >= 2 {
                                let vname = expect_symbol(&parts[0])?;
                                let val = self.evaluate(&parts[1])?;
                                self.env.insert(vname, val);
                            }
                        }
                    }
                    let result = self.evaluate(&body)?;
                    self.env = saved_env;
                    return Ok(result);
                }

                "progn" | "begin" => {
                    let mut result = Value::Term(self.arena.atom(BOT));
                    for expr in &items[1..] {
                        result = self.evaluate(expr)?;
                    }
                    return Ok(result);
                }

                "lambda" => {
                    if items.len() < 3 {
                        return Err("lambda requires params and body".to_string());
                    }
                    let params = expect_param_list(&items[1])?;
                    let body = if items.len() == 3 {
                        items[2].clone()
                    } else {
                        wrap_progn(&items[2..])
                    };
                    return Ok(Value::Function(Function {
                        params,
                        body,
                        closure: self.env.clone(), // O(1) Rc clone
                        name: None,
                    }));
                }

                "and" => {
                    let mut result = Value::Term(self.arena.atom(TOP));
                    for expr in &items[1..] {
                        result = self.evaluate(expr)?;
                        if let Value::Term(t) = &result {
                            if self.arena.get(*t) == Term::Atom(BOT) {
                                return Ok(Value::Term(self.arena.atom(BOT)));
                            }
                        }
                    }
                    return Ok(result);
                }

                "or" => {
                    for expr in &items[1..] {
                        let result = self.evaluate(expr)?;
                        if let Value::Term(t) = &result {
                            if self.arena.get(*t) != Term::Atom(BOT) {
                                return Ok(result);
                            }
                        } else {
                            return Ok(result); // Functions are truthy
                        }
                    }
                    return Ok(Value::Term(self.arena.atom(BOT)));
                }

                "not" => {
                    if items.len() != 2 {
                        return Err("not takes 1 argument".to_string());
                    }
                    let val = self.eval_to_term(&items[1])?;
                    if self.arena.get(val) == Term::Atom(BOT) {
                        return Ok(Value::Term(self.arena.atom(TOP)));
                    }
                    return Ok(Value::Term(self.arena.atom(BOT)));
                }

                "env-size" => {
                    return Ok(Value::Term(self.encode_int(self.env.len() as i64)));
                }

                "env-keys" => {
                    let bot = self.arena.atom(BOT);
                    let mut keys = self.env.keys();
                    keys.sort();
                    let mut result = bot;
                    for name in keys.iter().rev() {
                        let mut name_term = bot;
                        for c in name.chars().rev() {
                            let ch = self.encode_int(c as i64);
                            name_term = self.cons(ch, name_term);
                        }
                        result = self.cons(name_term, result);
                    }
                    return Ok(Value::Term(result));
                }

                "bound?" => {
                    if items.len() != 2 {
                        return Err("bound? takes 1 argument".to_string());
                    }
                    if let SExpr::Symbol(vname) = &items[1] {
                        let exists = self.env.contains_key(vname);
                        return Ok(Value::Term(self.arena.atom(if exists { TOP } else { BOT })));
                    }
                    return Ok(Value::Term(self.arena.atom(BOT)));
                }

                _ => {} // Fall through to function application
            }
        }

        // Function application: (fn args...)
        let fn_val = self.evaluate(head)?;
        let args: Vec<Value> = items[1..].iter()
            .map(|a| self.evaluate(a))
            .collect::<Result<Vec<_>, _>>()?;

        self.apply_fn(&fn_val, &args)
    }

    fn eval_define(&mut self, items: &[SExpr]) -> Result<Value, String> {
        if items.len() < 3 {
            return Err("define requires at least 2 args".to_string());
        }
        if let SExpr::List(sig) = &items[1] {
            let fname = expect_symbol(&sig[0])?;
            let params: Vec<String> = sig[1..].iter()
                .map(|p| expect_symbol(p))
                .collect::<Result<Vec<_>, _>>()?;
            let body = if items.len() == 3 {
                items[2].clone()
            } else {
                wrap_progn(&items[2..])
            };
            let func = Function {
                params,
                body,
                closure: self.env.clone(),
                name: Some(fname.clone()),
            };
            self.env.insert(fname, Value::Function(func));
            return Ok(Value::Term(VOID_TERM));
        }
        if let SExpr::Symbol(vname) = &items[1] {
            let val = self.evaluate(&items[2])?;
            self.env.insert(vname.clone(), val);
            return Ok(Value::Term(VOID_TERM));
        }
        Err("bad define form".to_string())
    }

    /// Evaluate an S-expression and extract the term (u32).
    /// Functions are not terms — this will error if result is a Function.
    fn eval_to_term(&mut self, sexpr: &SExpr) -> Result<u32, String> {
        match self.evaluate(sexpr)? {
            Value::Term(t) => Ok(t),
            Value::Builtin(_) => Err("builtin used as value".to_string()),
            Value::Function(_) => Err("function used as value".to_string()),
        }
    }

    fn value_to_term(&self, val: &Value) -> Result<u32, String> {
        match val {
            Value::Term(t) => Ok(*t),
            _ => Err("expected a term value".to_string()),
        }
    }

    fn apply_fn(&mut self, func: &Value, args: &[Value]) -> Result<Value, String> {
        match func {
            Value::Builtin(name) => {
                let term_args: Vec<u32> = args.iter()
                    .map(|a| self.value_to_term(a))
                    .collect::<Result<Vec<_>, _>>()?;
                let result = self.apply_builtin(name, &term_args)?;
                Ok(Value::Term(result))
            }
            Value::Function(f) => {
                if args.len() != f.params.len() {
                    return Err(format!(
                        "expected {} args, got {}",
                        f.params.len(), args.len()
                    ));
                }
                // Create child scope of closure env for this call's bindings.
                // The closure env is shared (Rc), the child is new and local.
                let call_env = Env::child(&f.closure);
                // Self-reference for recursion (visible via parent chain
                // for defun, but needed explicitly for anonymous recursion)
                if let Some(ref fname) = f.name {
                    call_env.insert(fname.clone(), Value::Function(f.clone()));
                }
                for (param, arg) in f.params.iter().zip(args) {
                    call_env.insert(param.clone(), arg.clone());
                }
                let saved_env = std::mem::replace(&mut self.env, call_env);
                let result = self.evaluate(&f.body)?;
                self.env = saved_env;
                Ok(result)
            }
            Value::Term(t) => Err(format!("not callable: {}", self.arena.display_lisp(*t))),
        }
    }

    fn apply_builtin(&mut self, name: &str, args: &[u32]) -> Result<u32, String> {
        match name {
            "+" => {
                let a = self.decode_int(args[0]).ok_or("+ requires numbers")?;
                let b = self.decode_int(args[1]).ok_or("+ requires numbers")?;
                Ok(self.encode_int(a + b))
            }
            "-" => {
                let a = self.decode_int(args[0]).ok_or("- requires numbers")?;
                let b = self.decode_int(args[1]).ok_or("- requires numbers")?;
                Ok(self.encode_int((a - b).max(0)))
            }
            "*" => {
                let a = self.decode_int(args[0]).ok_or("* requires numbers")?;
                let b = self.decode_int(args[1]).ok_or("* requires numbers")?;
                Ok(self.encode_int(a * b))
            }
            "<" => {
                let a = self.decode_int(args[0]).ok_or("< requires numbers")?;
                let b = self.decode_int(args[1]).ok_or("< requires numbers")?;
                Ok(self.arena.atom(if a < b { TOP } else { BOT }))
            }
            ">" => {
                let a = self.decode_int(args[0]).ok_or("> requires numbers")?;
                let b = self.decode_int(args[1]).ok_or("> requires numbers")?;
                Ok(self.arena.atom(if a > b { TOP } else { BOT }))
            }
            "<=" => {
                let a = self.decode_int(args[0]).ok_or("<= requires numbers")?;
                let b = self.decode_int(args[1]).ok_or("<= requires numbers")?;
                Ok(self.arena.atom(if a <= b { TOP } else { BOT }))
            }
            ">=" => {
                let a = self.decode_int(args[0]).ok_or(">= requires numbers")?;
                let b = self.decode_int(args[1]).ok_or(">= requires numbers")?;
                Ok(self.arena.atom(if a >= b { TOP } else { BOT }))
            }
            "=" | "eq" | "equal" => {
                let eq = self.arena.term_eq(args[0], args[1]);
                Ok(self.arena.atom(if eq { TOP } else { BOT }))
            }
            "cons" => Ok(self.cons(args[0], args[1])),
            "car" => {
                let f = self.arena.atom(F_ENC);
                let app = self.arena.app(f, args[0]);
                self.psi_eval(app).map_err(|e| e.to_string())
            }
            "cdr" => {
                let eta = self.arena.atom(ETA);
                let app = self.arena.app(eta, args[0]);
                self.psi_eval(app).map_err(|e| e.to_string())
            }
            "null" => {
                Ok(self.arena.atom(if self.arena.get(args[0]) == Term::Atom(BOT) { TOP } else { BOT }))
            }
            "zerop" => {
                let zero = self.encode_int(0);
                let eq = self.arena.term_eq(args[0], zero);
                Ok(self.arena.atom(if eq { TOP } else { BOT }))
            }
            "atom" => {
                Ok(self.arena.atom(if matches!(self.arena.get(args[0]), Term::Atom(_)) { TOP } else { BOT }))
            }
            "numberp" => {
                let is_num = self.decode_int(args[0]).is_some();
                Ok(self.arena.atom(if is_num { TOP } else { BOT }))
            }
            "display" => {
                let s = self.display(args[0]);
                for b in s.bytes() {
                    self.io.put(b);
                }
                self.io.flush();
                Ok(VOID_TERM)
            }
            "print" => {
                let s = self.display(args[0]);
                for b in s.bytes() {
                    self.io.put(b);
                }
                self.io.put(b'\n');
                self.io.flush();
                Ok(VOID_TERM)
            }
            "terpri" => {
                self.io.put(b'\n');
                self.io.flush();
                Ok(VOID_TERM)
            }
            "list" => {
                let bot = self.arena.atom(BOT);
                let mut result = bot;
                for &a in args.iter().rev() {
                    result = self.cons(a, result);
                }
                Ok(result)
            }
            "mod" => {
                let a = self.decode_int(args[0]).ok_or("mod requires numbers")?;
                let b = self.decode_int(args[1]).ok_or("mod requires numbers")?;
                if b == 0 { return Err("mod by zero".to_string()); }
                Ok(self.encode_int(a % b))
            }
            "/" => {
                let a = self.decode_int(args[0]).ok_or("/ requires numbers")?;
                let b = self.decode_int(args[1]).ok_or("/ requires numbers")?;
                if b == 0 { return Err("/ by zero".to_string()); }
                Ok(self.encode_int(a / b))
            }
            "1+" => {
                let a = self.decode_int(args[0]).ok_or("1+ requires a number")?;
                Ok(self.encode_int(a + 1))
            }
            "1-" => {
                let a = self.decode_int(args[0]).ok_or("1- requires a number")?;
                Ok(self.encode_int((a - 1).max(0)))
            }
            "write-char" => {
                let n = self.decode_int(args[0]).ok_or("write-char requires integer")?;
                if let Some(c) = char::from_u32(n as u32) {
                    let mut buf = [0u8; 4];
                    let s = c.encode_utf8(&mut buf);
                    for b in s.bytes() {
                        self.io.put(b);
                    }
                } else {
                    self.io.put(n as u8);
                }
                self.io.flush();
                Ok(VOID_TERM)
            }
            "write-string" => {
                let mut term = args[0];
                loop {
                    if let Some((car, cdr)) = self.arena.as_pair(term) {
                        if let Some(n) = self.decode_int(car) {
                            if let Some(c) = char::from_u32(n as u32) {
                                let mut buf = [0u8; 4];
                                let s = c.encode_utf8(&mut buf);
                                for b in s.bytes() {
                                    self.io.put(b);
                                }
                            } else {
                                self.io.put(n as u8);
                            }
                        }
                        term = cdr;
                    } else {
                        break;
                    }
                }
                self.io.flush();
                Ok(VOID_TERM)
            }
            "dot" => {
                let a = self.decode_int(args[0]).ok_or("dot requires integers (atom indices 0-15)")?;
                let b = self.decode_int(args[1]).ok_or("dot requires integers (atom indices 0-15)")?;
                if !(0..=15).contains(&a) || !(0..=15).contains(&b) {
                    return Err(format!("dot: indices must be 0-15, got {} and {}", a, b));
                }
                Ok(self.encode_int(self.table[a as usize][b as usize] as i64))
            }
            "atom-name" => {
                let a = self.decode_int(args[0]).ok_or("atom-name requires index 0-15")?;
                if !(0..=15).contains(&a) {
                    return Err(format!("atom-name requires index 0-15, got {}", a));
                }
                let name = self.names[a as usize];
                let bot = self.arena.atom(BOT);
                let mut result = bot;
                for c in name.chars().rev() {
                    let ch = self.encode_int(c as i64);
                    result = self.cons(ch, result);
                }
                Ok(result)
            }
            _ => Err(format!("unknown builtin: {}", name)),
        }
    }

    fn translate_datum(&mut self, sexpr: &SExpr) -> Result<u32, String> {
        match sexpr {
            SExpr::Int(n) => Ok(self.encode_int(*n)),
            SExpr::Symbol(name) => {
                let up = name.to_uppercase();
                if up == "NIL" {
                    Ok(self.arena.atom(BOT))
                } else if up == "T" {
                    Ok(self.arena.atom(TOP))
                } else {
                    let id = self.symbol_id(name);
                    Ok(self.encode_int(id))
                }
            }
            SExpr::List(items) => {
                if items.is_empty() {
                    return Ok(self.arena.atom(BOT));
                }
                let bot = self.arena.atom(BOT);
                let mut result = bot;
                for item in items.iter().rev() {
                    let elem = self.translate_datum(item)?;
                    result = self.cons(elem, result);
                }
                Ok(result)
            }
            SExpr::Str(_) => Err("string in datum".to_string()),
        }
    }

    fn symbol_id(&mut self, name: &str) -> i64 {
        if let Some(&id) = self.symbol_table.get(name) {
            id
        } else {
            let id = self.next_symbol_id;
            self.next_symbol_id += 1;
            self.symbol_table.insert(name.to_string(), id);
            id
        }
    }

    pub fn stats(&self) -> MachineStats {
        MachineStats {
            arena_size: self.arena.len(),
        }
    }
}

fn expect_symbol(sexpr: &SExpr) -> Result<String, String> {
    if let SExpr::Symbol(s) = sexpr {
        Ok(s.clone())
    } else {
        Err("expected a symbol".to_string())
    }
}

fn expect_param_list(sexpr: &SExpr) -> Result<Vec<String>, String> {
    if let SExpr::List(ps) = sexpr {
        ps.iter().map(|p| expect_symbol(p)).collect()
    } else {
        Err("expected a parameter list".to_string())
    }
}

fn wrap_progn(exprs: &[SExpr]) -> SExpr {
    let mut items = vec![SExpr::Symbol("progn".to_string())];
    items.extend_from_slice(exprs);
    SExpr::List(items)
}

fn decode_escape(s: &str) -> String {
    let mut out = String::new();
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c == '\\' {
            match it.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some('\\') => out.push('\\'),
                Some(x) => { out.push('\\'); out.push(x); }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}
