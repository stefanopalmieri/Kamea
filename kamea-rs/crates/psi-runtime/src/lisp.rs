use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use crate::machine::Value;

/// S-expression types.
#[derive(Clone, Debug)]
pub enum SExpr {
    Int(i64),
    Symbol(String),
    Str(String),
    List(Vec<SExpr>),
}

/// A scope frame in the linked environment chain.
pub struct EnvFrame {
    bindings: HashMap<String, Value>,
    parent: Option<Env>,
}

/// Rc-shared linked environment. Captures are O(1) pointer copies.
#[derive(Clone)]
pub struct Env(Rc<RefCell<EnvFrame>>);

impl Env {
    pub fn new() -> Self {
        Env(Rc::new(RefCell::new(EnvFrame {
            bindings: HashMap::new(),
            parent: None,
        })))
    }

    /// Create a child scope whose parent is `parent`.
    pub fn child(parent: &Env) -> Self {
        Env(Rc::new(RefCell::new(EnvFrame {
            bindings: HashMap::new(),
            parent: Some(parent.clone()),
        })))
    }

    /// Look up a name, walking the parent chain.
    pub fn get(&self, name: &str) -> Option<Value> {
        let frame = self.0.borrow();
        if let Some(val) = frame.bindings.get(name) {
            Some(val.clone())
        } else if let Some(ref parent) = frame.parent {
            parent.get(name)
        } else {
            None
        }
    }

    /// Insert a binding into the current (innermost) frame.
    pub fn insert(&self, name: String, val: Value) {
        self.0.borrow_mut().bindings.insert(name, val);
    }

    pub fn contains_key(&self, name: &str) -> bool {
        let frame = self.0.borrow();
        frame.bindings.contains_key(name)
            || frame.parent.as_ref().map_or(false, |p| p.contains_key(name))
    }

    pub fn len(&self) -> usize {
        let frame = self.0.borrow();
        let local = frame.bindings.len();
        local + frame.parent.as_ref().map_or(0, |p| p.len())
    }

    pub fn keys(&self) -> Vec<String> {
        let frame = self.0.borrow();
        let mut keys: Vec<String> = frame.bindings.keys().cloned().collect();
        if let Some(ref parent) = frame.parent {
            for k in parent.keys() {
                if !frame.bindings.contains_key(&k) {
                    keys.push(k);
                }
            }
        }
        keys
    }
}

impl std::fmt::Debug for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let frame = self.0.borrow();
        write!(f, "Env({} bindings", frame.bindings.len())?;
        if frame.parent.is_some() {
            write!(f, " + parent")?;
        }
        write!(f, ")")
    }
}

/// User-defined function.
#[derive(Clone, Debug)]
pub struct Function {
    pub params: Vec<String>,
    pub body: SExpr,
    pub closure: Env,
    pub name: Option<String>,
}

/// Tokenize Lisp source.
fn tokenize(source: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = source.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == ';' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '(' || c == ')' {
            tokens.push(c.to_string());
            i += 1;
        } else if c == '\'' {
            tokens.push("'".to_string());
            i += 1;
        } else if c == '"' {
            let mut j = i + 1;
            while j < chars.len() && chars[j] != '"' {
                if chars[j] == '\\' && j + 1 < chars.len() {
                    j += 1; // skip escaped char
                }
                j += 1;
            }
            let s: String = chars[i..=j.min(chars.len() - 1)].iter().collect();
            tokens.push(s);
            i = j + 1;
        } else {
            let mut j = i;
            while j < chars.len() && !chars[j].is_whitespace() && chars[j] != '(' && chars[j] != ')' && chars[j] != ';' {
                j += 1;
            }
            let s: String = chars[i..j].iter().collect();
            tokens.push(s);
            i = j;
        }
    }
    tokens
}

/// Parse tokens into an S-expression.
fn parse_one(tokens: &[String], pos: usize) -> Result<(SExpr, usize), String> {
    if pos >= tokens.len() {
        return Err("unexpected end of input".to_string());
    }

    let tok = &tokens[pos];

    if tok == "'" {
        let (expr, next) = parse_one(tokens, pos + 1)?;
        return Ok((SExpr::List(vec![SExpr::Symbol("quote".to_string()), expr]), next));
    }

    if tok == "(" {
        let mut items = Vec::new();
        let mut p = pos + 1;
        while p < tokens.len() && tokens[p] != ")" {
            let (expr, next) = parse_one(tokens, p)?;
            items.push(expr);
            p = next;
        }
        if p >= tokens.len() {
            return Err("missing closing )".to_string());
        }
        return Ok((SExpr::List(items), p + 1));
    }

    if tok == ")" {
        return Err("unexpected )".to_string());
    }

    // String literal
    if tok.starts_with('"') && tok.ends_with('"') && tok.len() >= 2 {
        let inner = tok[1..tok.len()-1].to_string();
        return Ok((SExpr::Str(inner), pos + 1));
    }

    // Integer
    if let Ok(n) = tok.parse::<i64>() {
        return Ok((SExpr::Int(n), pos + 1));
    }

    // Symbol
    Ok((SExpr::Symbol(tok.clone()), pos + 1))
}

/// Parse all top-level expressions from source.
pub fn parse_all(source: &str) -> Result<Vec<SExpr>, String> {
    let tokens = tokenize(source);
    let mut exprs = Vec::new();
    let mut pos = 0;
    while pos < tokens.len() {
        let (expr, next) = parse_one(&tokens, pos)?;
        exprs.push(expr);
        pos = next;
    }
    Ok(exprs)
}
