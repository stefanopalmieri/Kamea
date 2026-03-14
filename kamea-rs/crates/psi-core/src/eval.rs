use crate::table::{self, Q, G_ENC, E, F_ENC, ETA, RHO, Y_COMB};
use crate::term::{Arena, Term};

/// Evaluation configuration.
#[derive(Clone, Debug)]
pub struct EvalConfig {
    pub max_steps: usize,
}

impl Default for EvalConfig {
    fn default() -> Self {
        EvalConfig {
            max_steps: 100_000,
        }
    }
}

/// Evaluation errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    StepLimitExceeded { term: u32 },
}

impl core::fmt::Display for EvalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            EvalError::StepLimitExceeded { term } => {
                write!(f, "step limit exceeded at term {}", term)
            }
        }
    }
}

/// A single step result from the evaluator.
#[derive(Clone, Debug)]
pub enum StepResult {
    /// Evaluation complete, result is ready.
    Done(u32),
    /// One rule was applied; call step() again.
    Continue {
        rule: &'static str,
        term: u32,
    },
    /// Step limit exceeded.
    Error(EvalError),
}

/// Continuation frames for the explicit evaluation stack.
#[derive(Clone, Debug)]
enum Frame {
    /// Evaluate term at index, push result.
    Eval(u32),
    /// We have eval'd the arg of App(G_ENC, arg). Wrap result in App(G_ENC, _).
    WrapG,
    /// We have eval'd arg of App(E, arg). Apply E destructor.
    ApplyE,
    /// We have eval'd arg of App(F_ENC, arg). Apply f destructor.
    ApplyF,
    /// We have eval'd arg of App(ETA, arg). Apply η destructor.
    ApplyEta,
    /// We have eval'd arg of App(Y_COMB, arg). Wrap in App(Y, _).
    WrapY,
    /// We have eval'd arg of App(RHO, arg). Branch on result.
    /// Stores the ORIGINAL arg (before eval) for re-dispatch.
    BranchRho(u32),
    /// General application: we need to eval both sides.
    /// Phase 1: eval fn. Stores original fn and arg.
    EvalAppFn { orig_fn: u32, arg: u32 },
    /// Phase 2: eval arg. Stores evaluated fn and original fn.
    EvalAppArg { fn_val: u32, orig_fn: u32 },
    /// Phase 3: combine fn_val and arg_val.
    CombineApp { fn_val: u32 },
}

/// Explicit-stack evaluator. Supports single-stepping for debugger.
pub struct Evaluator {
    stack: Vec<Frame>,
    /// The result register — holds intermediate values between frames.
    result: Option<u32>,
    steps: usize,
}

impl Evaluator {
    /// Create a new evaluator for the given term.
    pub fn new(term: u32) -> Self {
        Evaluator {
            stack: vec![Frame::Eval(term)],
            result: None,
            steps: 0,
        }
    }

    /// Is evaluation complete?
    pub fn is_done(&self) -> bool {
        self.stack.is_empty() && self.result.is_some()
    }

    /// Get the final result (only valid after is_done() returns true).
    pub fn get_result(&self) -> Option<u32> {
        if self.stack.is_empty() {
            self.result
        } else {
            None
        }
    }

    /// Current stack depth.
    pub fn depth(&self) -> usize {
        self.stack.len()
    }

    /// Number of steps executed.
    pub fn step_count(&self) -> usize {
        self.steps
    }

    /// Execute one evaluation step.
    pub fn step(&mut self, arena: &mut Arena, config: &EvalConfig) -> StepResult {
        self.steps += 1;
        if self.steps > config.max_steps {
            let term = match self.stack.last() {
                Some(Frame::Eval(t)) => *t,
                _ => 0,
            };
            return StepResult::Error(EvalError::StepLimitExceeded { term });
        }

        let frame = match self.stack.pop() {
            Some(f) => f,
            None => {
                return StepResult::Done(self.result.unwrap_or(0));
            }
        };

        match frame {
            Frame::Eval(term) => {
                match arena.get(term) {
                    // Atom self-evaluation
                    Term::Atom(_) => {
                        self.result = Some(term);
                        StepResult::Continue { rule: "atom", term }
                    }

                    Term::App { fun, arg } => {
                        match arena.get(fun) {
                            // Q: freeze (lazy)
                            Term::Atom(Q) => {
                                self.result = Some(term);
                                StepResult::Continue { rule: "Q-freeze", term }
                            }

                            // g: pair constructor
                            Term::Atom(G_ENC) => {
                                self.stack.push(Frame::WrapG);
                                self.stack.push(Frame::Eval(arg));
                                StepResult::Continue { rule: "g-construct", term }
                            }

                            // E: predecessor/unwrap
                            Term::Atom(E) => {
                                self.stack.push(Frame::ApplyE);
                                self.stack.push(Frame::Eval(arg));
                                StepResult::Continue { rule: "E-eval-arg", term }
                            }

                            // f: fst
                            Term::Atom(F_ENC) => {
                                self.stack.push(Frame::ApplyF);
                                self.stack.push(Frame::Eval(arg));
                                StepResult::Continue { rule: "f-eval-arg", term }
                            }

                            // η: snd
                            Term::Atom(ETA) => {
                                self.stack.push(Frame::ApplyEta);
                                self.stack.push(Frame::Eval(arg));
                                StepResult::Continue { rule: "η-eval-arg", term }
                            }

                            // Y: fixed-point
                            Term::Atom(Y_COMB) => {
                                self.stack.push(Frame::WrapY);
                                self.stack.push(Frame::Eval(arg));
                                StepResult::Continue { rule: "Y-eval-arg", term }
                            }

                            // ρ: structural branch
                            Term::Atom(RHO) => {
                                self.stack.push(Frame::BranchRho(arg));
                                self.stack.push(Frame::Eval(arg));
                                StepResult::Continue { rule: "ρ-eval-arg", term }
                            }

                            // General: fn is a non-special atom
                            Term::Atom(_) => {
                                // Eval the arg, then dot
                                self.stack.push(Frame::CombineApp { fn_val: fun });
                                self.stack.push(Frame::Eval(arg));
                                StepResult::Continue { rule: "app-atom-fn", term }
                            }

                            // General: fn is compound
                            Term::App { .. } => {
                                self.stack.push(Frame::EvalAppFn { orig_fn: fun, arg });
                                self.stack.push(Frame::Eval(fun));
                                StepResult::Continue { rule: "app-eval-fn", term }
                            }
                        }
                    }
                }
            }

            Frame::WrapG => {
                let val = self.result.unwrap();
                let g = arena.atom(G_ENC);
                let wrapped = arena.app(g, val);
                self.result = Some(wrapped);
                StepResult::Continue { rule: "g-wrap", term: wrapped }
            }

            Frame::ApplyE => {
                let val = self.result.unwrap();
                match arena.get(val) {
                    Term::App { fun, arg } if arena.get(fun) == Term::Atom(Q) => {
                        // E unwraps Q: eval the inner
                        self.stack.push(Frame::Eval(arg));
                        StepResult::Continue { rule: "E-unwrap-Q", term: val }
                    }
                    Term::Atom(a) => {
                        let result = arena.atom(table::dot(E, a));
                        self.result = Some(result);
                        StepResult::Continue { rule: "E-dot", term: result }
                    }
                    _ => {
                        let e = arena.atom(E);
                        let irr = arena.app(e, val);
                        self.result = Some(irr);
                        StepResult::Continue { rule: "E-irreducible", term: irr }
                    }
                }
            }

            Frame::ApplyF => {
                let val = self.result.unwrap();
                if let Some((car, _cdr)) = arena.as_pair(val) {
                    self.stack.push(Frame::Eval(car));
                    StepResult::Continue { rule: "f-extract-car", term: val }
                } else {
                    match arena.get(val) {
                        Term::Atom(a) => {
                            let result = arena.atom(table::dot(F_ENC, a));
                            self.result = Some(result);
                            StepResult::Continue { rule: "f-dot", term: result }
                        }
                        _ => {
                            let f = arena.atom(F_ENC);
                            let irr = arena.app(f, val);
                            self.result = Some(irr);
                            StepResult::Continue { rule: "f-irreducible", term: irr }
                        }
                    }
                }
            }

            Frame::ApplyEta => {
                let val = self.result.unwrap();
                if let Some((_car, cdr)) = arena.as_pair(val) {
                    self.stack.push(Frame::Eval(cdr));
                    StepResult::Continue { rule: "η-extract-cdr", term: val }
                } else {
                    match arena.get(val) {
                        Term::Atom(a) => {
                            let result = arena.atom(table::dot(ETA, a));
                            self.result = Some(result);
                            StepResult::Continue { rule: "η-dot", term: result }
                        }
                        _ => {
                            let eta = arena.atom(ETA);
                            let irr = arena.app(eta, val);
                            self.result = Some(irr);
                            StepResult::Continue { rule: "η-irreducible", term: irr }
                        }
                    }
                }
            }

            Frame::WrapY => {
                let val = self.result.unwrap();
                let y = arena.atom(Y_COMB);
                let wrapped = arena.app(y, val);
                self.result = Some(wrapped);
                StepResult::Continue { rule: "Y-wrap", term: wrapped }
            }

            Frame::BranchRho(orig_arg) => {
                let val = self.result.unwrap();
                match arena.get(val) {
                    Term::Atom(_) => {
                        // atom → f-path
                        let f = arena.atom(F_ENC);
                        let app = arena.app(f, orig_arg);
                        self.stack.push(Frame::Eval(app));
                        StepResult::Continue { rule: "ρ-atom→f", term: val }
                    }
                    Term::App { .. } => {
                        // compound → g-path
                        let g = arena.atom(G_ENC);
                        let app = arena.app(g, orig_arg);
                        self.stack.push(Frame::Eval(app));
                        StepResult::Continue { rule: "ρ-compound→g", term: val }
                    }
                }
            }

            Frame::EvalAppFn { orig_fn, arg } => {
                let fn_val = self.result.unwrap();

                // If fn reduced to an atom, re-dispatch
                if let Term::Atom(_) = arena.get(fn_val) {
                    if arena.get(orig_fn) != arena.get(fn_val) {
                        // fn reduced to a different atom — need to eval arg then re-dispatch
                        self.stack.push(Frame::EvalAppArg { fn_val, orig_fn });
                        self.stack.push(Frame::Eval(arg));
                        return StepResult::Continue { rule: "app-fn-reduced", term: fn_val };
                    }
                }

                // Curried g check
                if let Term::App { fun: gfun, .. } = arena.get(fn_val) {
                    if arena.get(gfun) == Term::Atom(G_ENC) {
                        // (g·a)·b — eval arg, then combine as pair
                        self.stack.push(Frame::CombineApp { fn_val });
                        self.stack.push(Frame::Eval(arg));
                        return StepResult::Continue { rule: "app-curried-g", term: fn_val };
                    }
                }

                // Default: eval arg
                self.stack.push(Frame::EvalAppArg { fn_val, orig_fn });
                self.stack.push(Frame::Eval(arg));
                StepResult::Continue { rule: "app-eval-arg", term: fn_val }
            }

            Frame::EvalAppArg { fn_val, orig_fn } => {
                let arg_val = self.result.unwrap();

                // If fn reduced to an atom that wasn't originally an atom, re-dispatch
                if let Term::Atom(_) = arena.get(fn_val) {
                    if arena.get(orig_fn) != arena.get(fn_val) {
                        let new_app = arena.app(fn_val, arg_val);
                        self.stack.push(Frame::Eval(new_app));
                        return StepResult::Continue { rule: "app-redispatch", term: new_app };
                    }
                }

                // Curried g: (g·a)·b = pair
                if let Term::App { fun: gfun, .. } = arena.get(fn_val) {
                    if arena.get(gfun) == Term::Atom(G_ENC) {
                        let pair = arena.app(fn_val, arg_val);
                        self.result = Some(pair);
                        return StepResult::Continue { rule: "pair-construct", term: pair };
                    }
                }

                match (arena.get(fn_val), arena.get(arg_val)) {
                    (Term::Atom(a), Term::Atom(b)) => {
                        let result = arena.atom(table::dot(a, b));
                        self.result = Some(result);
                        StepResult::Continue { rule: "dot-lookup", term: result }
                    }
                    _ => {
                        let result = arena.app(fn_val, arg_val);
                        self.result = Some(result);
                        StepResult::Continue { rule: "app-irreducible", term: result }
                    }
                }
            }

            Frame::CombineApp { fn_val } => {
                let arg_val = self.result.unwrap();

                // Curried g: (g·a)·b = pair
                if let Term::App { fun: gfun, .. } = arena.get(fn_val) {
                    if arena.get(gfun) == Term::Atom(G_ENC) {
                        let pair = arena.app(fn_val, arg_val);
                        self.result = Some(pair);
                        return StepResult::Continue { rule: "pair-construct", term: pair };
                    }
                }

                match (arena.get(fn_val), arena.get(arg_val)) {
                    (Term::Atom(a), Term::Atom(b)) => {
                        let result = arena.atom(table::dot(a, b));
                        self.result = Some(result);
                        StepResult::Continue { rule: "dot-lookup", term: result }
                    }
                    _ => {
                        let result = arena.app(fn_val, arg_val);
                        self.result = Some(result);
                        StepResult::Continue { rule: "app-irreducible", term: result }
                    }
                }
            }
        }
    }

    /// Run to completion.
    pub fn run(&mut self, arena: &mut Arena, config: &EvalConfig) -> Result<u32, EvalError> {
        loop {
            match self.step(arena, config) {
                StepResult::Done(result) => return Ok(result),
                StepResult::Continue { .. } => continue,
                StepResult::Error(e) => return Err(e),
            }
        }
    }
}

/// Convenience: evaluate a term to completion.
pub fn eval(arena: &mut Arena, term: u32, config: &EvalConfig) -> Result<u32, EvalError> {
    let mut evaluator = Evaluator::new(term);
    evaluator.run(arena, config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::table::*;

    fn cfg() -> EvalConfig {
        EvalConfig::default()
    }

    #[test]
    fn test_atom_self_eval() {
        let mut arena = Arena::new(64);
        let config = cfg();
        for a in 0..16u8 {
            let t = arena.atom(a);
            let r = eval(&mut arena, t, &config).unwrap();
            assert_eq!(arena.get(r), Term::Atom(a));
        }
    }

    #[test]
    fn test_dot_non_special_pairs() {
        let special = [Q, G_ENC, E, F_ENC, ETA, RHO, Y_COMB];
        let mut arena = Arena::new(4096);
        let config = cfg();
        for a in 0..16u8 {
            if special.contains(&a) {
                continue;
            }
            for b in 0..16u8 {
                let ta = arena.atom(a);
                let tb = arena.atom(b);
                let app = arena.app(ta, tb);
                let r = eval(&mut arena, app, &config).unwrap();
                assert_eq!(arena.get(r), Term::Atom(dot(a, b)),
                    "dot({}, {}) expected {} got {:?}", a, b, dot(a, b), arena.get(r));
            }
        }
    }

    #[test]
    fn test_q_lazy() {
        let mut arena = Arena::new(64);
        let config = cfg();
        let tau = arena.atom(TAU);
        let q = arena.atom(Q);
        let app = arena.app(q, tau);
        let r = eval(&mut arena, app, &config).unwrap();
        match arena.get(r) {
            Term::App { fun, arg } => {
                assert_eq!(arena.get(fun), Term::Atom(Q));
                assert_eq!(arena.get(arg), Term::Atom(TAU));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn test_e_unwraps_q() {
        let mut arena = Arena::new(64);
        let config = cfg();
        let tau = arena.atom(TAU);
        let q = arena.atom(Q);
        let qt = arena.app(q, tau);
        let e = arena.atom(E);
        let app = arena.app(e, qt);
        let r = eval(&mut arena, app, &config).unwrap();
        assert_eq!(arena.get(r), Term::Atom(TAU));
    }

    #[test]
    fn test_pair_fst_snd() {
        let mut arena = Arena::new(128);
        let config = cfg();
        let a3 = arena.atom(TAU);
        let a5 = arena.atom(5);
        let p = arena.pair(a3, a5);

        let f = arena.atom(F_ENC);
        let fst_app = arena.app(f, p);
        let r = eval(&mut arena, fst_app, &config).unwrap();
        assert_eq!(arena.get(r), Term::Atom(TAU));

        let eta = arena.atom(ETA);
        let snd_app = arena.app(eta, p);
        let r = eval(&mut arena, snd_app, &config).unwrap();
        assert_eq!(arena.get(r), Term::Atom(5));
    }

    #[test]
    fn test_natural_numbers() {
        let mut arena = Arena::new(256);
        for n in 0..10u64 {
            let t = arena.nat(n);
            assert_eq!(arena.to_nat(t), Some(n), "nat({}) roundtrip failed", n);
        }
    }

    #[test]
    fn test_successor_predecessor() {
        let mut arena = Arena::new(256);
        let config = cfg();
        for n in 1..8u64 {
            let nat_n = arena.nat(n);
            let e = arena.atom(E);
            let app = arena.app(e, nat_n);
            let r = eval(&mut arena, app, &config).unwrap();
            assert_eq!(arena.to_nat(r), Some(n - 1), "pred(nat({})) failed", n);
        }
    }

    #[test]
    fn test_nested_pair_state() {
        let mut arena = Arena::new(512);
        let config = cfg();
        let c0 = arena.nat(3);
        let c1 = arena.nat(5);
        let pc = arena.nat(2);
        let inner = arena.pair(c0, c1);
        let state = arena.pair(inner, pc);

        let f = arena.atom(F_ENC);
        let fst_app = arena.app(f, state);
        let inner_r = eval(&mut arena, fst_app, &config).unwrap();

        let f2 = arena.atom(F_ENC);
        let fst2 = arena.app(f2, inner_r);
        let c0_r = eval(&mut arena, fst2, &config).unwrap();
        assert_eq!(arena.to_nat(c0_r), Some(3));

        let eta = arena.atom(ETA);
        let snd = arena.app(eta, inner_r);
        let c1_r = eval(&mut arena, snd, &config).unwrap();
        assert_eq!(arena.to_nat(c1_r), Some(5));

        let eta2 = arena.atom(ETA);
        let snd2 = arena.app(eta2, state);
        let pc_r = eval(&mut arena, snd2, &config).unwrap();
        assert_eq!(arena.to_nat(pc_r), Some(2));
    }

    #[test]
    fn test_evaluator_stepping() {
        let mut arena = Arena::new(128);
        let config = cfg();
        // eval(App(E, App(Q, Atom(3)))) should give Atom(3)
        let tau = arena.atom(TAU);
        let q = arena.atom(Q);
        let qt = arena.app(q, tau);
        let e = arena.atom(E);
        let app = arena.app(e, qt);

        let mut evaluator = Evaluator::new(app);
        let mut steps = 0;
        loop {
            match evaluator.step(&mut arena, &config) {
                StepResult::Done(r) => {
                    assert_eq!(arena.get(r), Term::Atom(TAU));
                    break;
                }
                StepResult::Continue { rule, .. } => {
                    steps += 1;
                    assert!(steps < 100, "too many steps");
                }
                StepResult::Error(e) => panic!("error: {:?}", e),
            }
        }
        assert!(steps > 0, "should take at least one step");
    }
}
