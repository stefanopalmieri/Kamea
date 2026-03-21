use crate::table::{NAMES, Q, G_ENC, TOP, BOT};

/// Term representation. Arena-allocated for cache friendliness.
/// Atoms are indices 0-15 stored inline. App nodes reference arena slots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Term {
    Atom(u8),
    App { fun: u32, arg: u32 },
}

/// Fixed-size arena for term allocation.
pub struct Arena {
    nodes: Vec<Term>,
}

impl Arena {
    pub fn new(capacity: usize) -> Self {
        Arena {
            nodes: Vec::with_capacity(capacity),
        }
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn alloc(&mut self, term: Term) -> u32 {
        let idx = self.nodes.len() as u32;
        self.nodes.push(term);
        idx
    }

    pub fn get(&self, idx: u32) -> Term {
        self.nodes[idx as usize]
    }

    pub fn app(&mut self, fun: u32, arg: u32) -> u32 {
        self.alloc(Term::App { fun, arg })
    }

    pub fn atom(&mut self, a: u8) -> u32 {
        self.alloc(Term::Atom(a))
    }

    /// Build a Q-chain natural number: zero = Atom(TOP), succ(n) = App(Q, n).
    pub fn nat(&mut self, n: u64) -> u32 {
        let mut t = self.atom(TOP);
        for _ in 0..n {
            let q = self.atom(Q);
            t = self.app(q, t);
        }
        t
    }

    /// Decode a Q-chain natural. None if not a nat.
    pub fn to_nat(&self, mut idx: u32) -> Option<u64> {
        let mut count = 0u64;
        loop {
            match self.get(idx) {
                Term::Atom(a) => {
                    return if a == TOP { Some(count) } else { None };
                }
                Term::App { fun, arg } => {
                    if let Term::Atom(Q) = self.get(fun) {
                        // Note: Q constant is 6
                        if self.get(fun) == Term::Atom(Q) {
                            count += 1;
                            idx = arg;
                        } else {
                            return None;
                        }
                    } else {
                        return None;
                    }
                }
            }
        }
    }

    /// Build a curried pair: pair(a, b) = App(App(g, a), b).
    pub fn pair(&mut self, car: u32, cdr: u32) -> u32 {
        let g = self.atom(G_ENC);
        let ga = self.app(g, car);
        self.app(ga, cdr)
    }

    /// Check if term is a pair App(App(g, a), b) and return (a, b).
    pub fn as_pair(&self, idx: u32) -> Option<(u32, u32)> {
        if let Term::App { fun, arg } = self.get(idx) {
            if let Term::App { fun: gfun, arg: a } = self.get(fun) {
                if self.get(gfun) == Term::Atom(G_ENC) {
                    return Some((a, arg));
                }
            }
        }
        None
    }

    /// Display a term as a string.
    pub fn display_term(&self, idx: u32, max_depth: usize) -> String {
        if max_depth == 0 {
            return "...".to_string();
        }
        match self.get(idx) {
            Term::Atom(a) => NAMES[a as usize].to_string(),
            Term::App { fun, arg } => {
                format!(
                    "({} · {})",
                    self.display_term(fun, max_depth - 1),
                    self.display_term(arg, max_depth - 1)
                )
            }
        }
    }

    /// Encode integer in Ψ-Lisp convention: 0 = App(Q, TOP), n = (n+1) Q layers around TOP.
    pub fn encode_int(&mut self, n: u64) -> u32 {
        let mut t = self.atom(TOP);
        for _ in 0..=n {
            let q = self.atom(Q);
            t = self.app(q, t);
        }
        t
    }

    /// Decode integer in Ψ-Lisp convention: count Q layers, must be >= 1, core must be TOP.
    pub fn decode_int(&self, mut idx: u32) -> Option<i64> {
        let mut count = 0i64;
        loop {
            match self.get(idx) {
                Term::Atom(a) => {
                    if a == TOP && count >= 1 {
                        return Some(count - 1);
                    }
                    return None;
                }
                Term::App { fun, arg } => {
                    if self.get(fun) == Term::Atom(Q) {
                        count += 1;
                        idx = arg;
                    } else {
                        return None;
                    }
                }
            }
        }
    }

    /// Check if term is a proper list (NIL-terminated pair chain).
    pub fn is_proper_list(&self, mut idx: u32) -> bool {
        loop {
            match self.get(idx) {
                Term::Atom(a) => return a == BOT,
                Term::App { fun, arg } => {
                    if let Term::App { fun: gfun, arg: _ } = self.get(fun) {
                        if self.get(gfun) == Term::Atom(G_ENC) {
                            idx = arg;
                            continue;
                        }
                    }
                    return false;
                }
            }
        }
    }

    /// Get list elements from a proper list.
    pub fn list_elements(&self, mut idx: u32) -> Vec<u32> {
        let mut elems = Vec::new();
        loop {
            if let Some((car, cdr)) = self.as_pair(idx) {
                elems.push(car);
                idx = cdr;
            } else {
                break;
            }
        }
        elems
    }

    /// Display a term in Ψ-Lisp format.
    pub fn display_lisp(&self, idx: u32) -> String {
        let term = self.get(idx);
        match term {
            Term::Atom(a) if a == BOT => "NIL".to_string(),
            Term::Atom(a) if a == TOP => "T".to_string(),
            Term::Atom(a) => NAMES[a as usize].to_string(),
            _ => {
                // Check for integer
                if let Some(n) = self.decode_int(idx) {
                    return n.to_string();
                }
                // Check for proper list
                if self.is_proper_list(idx) {
                    if self.as_pair(idx).is_some() {
                        let elems = self.list_elements(idx);
                        let strs: Vec<String> = elems.iter().map(|&e| self.display_lisp(e)).collect();
                        return format!("({})", strs.join(" "));
                    }
                }
                // Check for dotted pair
                if let Some((car, cdr)) = self.as_pair(idx) {
                    return format!("({} . {})", self.display_lisp(car), self.display_lisp(cdr));
                }
                // Fallback
                self.display_term(idx, 30)
            }
        }
    }

    /// Deep equality check for two terms in the arena.
    pub fn term_eq(&self, a: u32, b: u32) -> bool {
        match (self.get(a), self.get(b)) {
            (Term::Atom(x), Term::Atom(y)) => x == y,
            (Term::App { fun: f1, arg: a1 }, Term::App { fun: f2, arg: a2 }) => {
                self.term_eq(f1, f2) && self.term_eq(a1, a2)
            }
            _ => false,
        }
    }
}
