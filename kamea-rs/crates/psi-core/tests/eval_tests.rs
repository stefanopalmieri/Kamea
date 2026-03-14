use psi_core::eval::{eval, EvalConfig};
use psi_core::table::*;
use psi_core::term::{Arena, Term};

fn cfg() -> EvalConfig {
    EvalConfig { max_steps: 100_000 }
}

#[test]
fn test_cayley_table_row0_all_zero() {
    // Row 0 (⊤) is all zeros — ⊤ is a left absorber.
    for b in 0..16u8 {
        assert_eq!(dot(TOP, b), TOP, "dot(⊤, {}) should be ⊤", b);
    }
}

#[test]
fn test_cayley_table_row1_all_one() {
    // Row 1 (⊥) is all ones — ⊥ is a left absorber.
    for b in 0..16u8 {
        assert_eq!(dot(BOT, b), BOT, "dot(⊥, {}) should be ⊥", b);
    }
}

#[test]
fn test_q_e_inverse() {
    // For all n: E(Q(n)) = n (QE inverse property)
    let mut arena = Arena::new(1024);
    let config = cfg();
    for n in 0..20u64 {
        let nat_n = arena.nat(n);
        let q = arena.atom(Q);
        let qn = arena.app(q, nat_n);
        let e = arena.atom(E);
        let eqn = arena.app(e, qn);
        let result = eval(&mut arena, eqn, &config).unwrap();
        assert_eq!(arena.to_nat(result), Some(n), "E(Q(nat({}))) should give nat({})", n, n);
    }
}

#[test]
fn test_pair_round_trip() {
    // For all (a, b): fst(pair(a, b)) = a, snd(pair(a, b)) = b
    let mut arena = Arena::new(4096);
    let config = cfg();
    for a in 0..8u64 {
        for b in 0..8u64 {
            let na = arena.nat(a);
            let nb = arena.nat(b);
            let p = arena.pair(na, nb);

            let f = arena.atom(F_ENC);
            let fst_app = arena.app(f, p);
            let fst_r = eval(&mut arena, fst_app, &config).unwrap();
            assert_eq!(arena.to_nat(fst_r), Some(a), "fst(pair({}, {})) failed", a, b);

            let eta = arena.atom(ETA);
            let snd_app = arena.app(eta, p);
            let snd_r = eval(&mut arena, snd_app, &config).unwrap();
            assert_eq!(arena.to_nat(snd_r), Some(b), "snd(pair({}, {})) failed", a, b);
        }
    }
}

#[test]
fn test_rho_atom_branch() {
    // ρ(atom) → f-path
    let mut arena = Arena::new(256);
    let config = cfg();
    let rho = arena.atom(RHO);
    let top = arena.atom(TOP);
    let app = arena.app(rho, top);
    let result = eval(&mut arena, app, &config).unwrap();
    // ρ(⊤) → f(⊤) = dot(f, ⊤) = 5
    assert_eq!(arena.get(result), Term::Atom(dot(F_ENC, TOP)));
}

#[test]
fn test_rho_compound_branch() {
    // ρ(compound) → g-path
    let mut arena = Arena::new(256);
    let config = cfg();
    let rho = arena.atom(RHO);
    let q = arena.atom(Q);
    let top = arena.atom(TOP);
    let qt = arena.app(q, top);  // Q(⊤) is compound
    let app = arena.app(rho, qt);
    let result = eval(&mut arena, app, &config).unwrap();
    // ρ(Q(⊤)) → g(Q(⊤)) = App(g, Q(⊤)) — g evaluates its arg
    // Q(⊤) is already a value (Q is lazy), so result is App(g, App(Q, ⊤))
    match arena.get(result) {
        Term::App { fun, arg } => {
            assert_eq!(arena.get(fun), Term::Atom(G_ENC));
            // arg should be App(Q, ⊤)
            match arena.get(arg) {
                Term::App { fun: qf, arg: qa } => {
                    assert_eq!(arena.get(qf), Term::Atom(Q));
                    assert_eq!(arena.get(qa), Term::Atom(TOP));
                }
                _ => panic!("expected App(Q, ⊤)"),
            }
        }
        _ => panic!("expected App(g, ...)"),
    }
}

#[test]
fn test_encode_decode_int() {
    // Mini-Lisp integer convention: 0 = App(Q, ⊤), n = (n+1) Q layers
    let mut arena = Arena::new(1024);
    for n in 0..50i64 {
        let encoded = arena.encode_int(n as u64);
        let decoded = arena.decode_int(encoded);
        assert_eq!(decoded, Some(n), "encode_int/decode_int roundtrip failed for {}", n);
    }
}

#[test]
fn test_2cm_simple_increment() {
    // Simulate: INC0, INC0, INC0, HALT → c0=3
    let mut arena = Arena::new(4096);
    let config = cfg();

    // Initial state: pair(pair(0, 0), 0)
    let zero = arena.nat(0);
    let zero2 = arena.nat(0);
    let zero3 = arena.nat(0);
    let inner = arena.pair(zero, zero2);
    let mut state = arena.pair(inner, zero3);

    for _ in 0..3 {
        // Extract c0 from state
        let f = arena.atom(F_ENC);
        let fst_app = arena.app(f, state);
        let inner = eval(&mut arena, fst_app, &config).unwrap();

        let f2 = arena.atom(F_ENC);
        let fst2 = arena.app(f2, inner);
        let c0 = eval(&mut arena, fst2, &config).unwrap();

        let eta = arena.atom(ETA);
        let snd = arena.app(eta, inner);
        let c1 = eval(&mut arena, snd, &config).unwrap();

        let eta2 = arena.atom(ETA);
        let snd2 = arena.app(eta2, state);
        let pc = eval(&mut arena, snd2, &config).unwrap();

        // INC c0: c0 = App(Q, c0)
        let q = arena.atom(Q);
        let new_c0 = arena.app(q, c0);
        // INC pc
        let q2 = arena.atom(Q);
        let new_pc = arena.app(q2, pc);

        let new_inner = arena.pair(new_c0, c1);
        state = arena.pair(new_inner, new_pc);
    }

    // Extract final c0
    let f = arena.atom(F_ENC);
    let fst_app = arena.app(f, state);
    let inner = eval(&mut arena, fst_app, &config).unwrap();
    let f2 = arena.atom(F_ENC);
    let fst2 = arena.app(f2, inner);
    let c0 = eval(&mut arena, fst2, &config).unwrap();
    assert_eq!(arena.to_nat(c0), Some(3));
}
