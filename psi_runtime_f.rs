// psi_runtime_f.rs — Ψ₁₆ᶠ runtime for compiled Ψ∗ programs (Rust).
//
// Two layers:
//   1. Cayley table (256 bytes) — the finite algebra (Ψ₁₆ᶠ / "full" table)
//   2. Cons cells (arena) — the term algebra (lists, pairs)
//
// Note: Arena is a bump allocator with no garbage collection.
// Phase 2 will replace this with MMTk for production use.
// The allocation API (arena.cons, arena.car, arena.cdr) will
// remain the same — only the backing implementation changes.

#![allow(dead_code)]

// ── Value representation ─────────────────────────────────────────
// All values are i64. Numbers are plain integers.
// NIL is a special sentinel. Cons cells use a tag bit.

pub type PsiVal = i64;

pub const PSI_NIL: PsiVal = i64::MIN;
pub const PSI_CONS_TAG: PsiVal = 1_i64 << 62;

#[inline(always)]
pub fn is_nil(x: PsiVal) -> bool { x == PSI_NIL }

#[inline(always)]
pub fn is_cons(x: PsiVal) -> bool { (x & PSI_CONS_TAG) != 0 && x != PSI_NIL }

#[inline(always)]
pub fn is_true(x: PsiVal) -> bool { x != PSI_NIL }

// ── Cayley table (Ψ₁₆ᶠ) ────────────────────────────────────────

pub const PSI_TOP: u8 = 0;
pub const PSI_BOT: u8 = 1;
pub const PSI_INC: u8 = 13;
pub const PSI_INV: u8 = 14;
pub const PSI_DEC: u8 = 15;

pub static PSI_CAYLEY: [[u8; 16]; 16] = [
    [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [ 5, 1,13, 7,11, 5, 6, 8, 2, 5,11, 9, 4,14, 3,15],
    [ 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1],
    [ 0,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],
    [ 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0],
    [15, 0, 5, 9, 3,15,14,14, 2,12, 8,14,12, 4,12, 8],
    [ 0, 1, 8, 4,13, 2,11, 2,14, 3,15,12,14,15, 6, 5],
    [12, 1,13, 7,11, 5,12,11, 4,12, 5,14,15, 7,11,12],
    [ 1, 6,14,14,14,14, 9, 8, 3,15, 5, 7,13,11,12, 4],
    [13, 1, 4, 3,12,11, 2,11, 5, 3, 8,14, 9, 7,11,11],
    [14, 1, 9,10,11,13,12, 7, 5, 6, 8, 2,14,12,10, 4],
    [ 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    [ 3, 0,14, 4,14, 6,11,12, 7, 3,15,10,14, 2, 6, 8],
    [14, 0, 5, 4, 3, 2,12, 5,11,14, 3,14,12, 2, 6, 3],
    [ 1, 3,13,15, 3, 7,14, 8,15, 4,11, 6, 7,14,12,10],
];

#[inline(always)]
pub fn psi_dot(a: u8, b: u8) -> u8 {
    PSI_CAYLEY[a as usize][b as usize]
}

// ── Arithmetic helpers for INC/DEC/INV on core {2,3,4,5} ────────
// Single arithmetic expressions — rustc optimizes them well.
// For non-core arguments, fall back to the Cayley table.

#[inline(always)]
pub fn psi_inc(x: u8) -> u8 {
    if x >= 2 && x <= 5 { ((x.wrapping_sub(1)) & 3) + 2 }
    else { PSI_CAYLEY[PSI_INC as usize][x as usize] }
}

#[inline(always)]
pub fn psi_dec(x: u8) -> u8 {
    if x >= 2 && x <= 5 { ((x.wrapping_sub(3)) & 3) + 2 }
    else { PSI_CAYLEY[PSI_DEC as usize][x as usize] }
}

#[inline(always)]
pub fn psi_inv(x: u8) -> u8 {
    if x >= 2 && x <= 5 { 7 - x }
    else { PSI_CAYLEY[PSI_INV as usize][x as usize] }
}

// ── Cons cell arena ──────────────────────────────────────────────

pub struct Arena {
    cells: Vec<(PsiVal, PsiVal)>,
}

impl Arena {
    pub fn new() -> Self {
        Arena { cells: Vec::with_capacity(1_000_000) }
    }

    #[inline]
    pub fn cons(&mut self, car: PsiVal, cdr: PsiVal) -> PsiVal {
        let idx = self.cells.len();
        self.cells.push((car, cdr));
        PSI_CONS_TAG | (idx as PsiVal)
    }

    #[inline]
    pub fn car(&self, cell: PsiVal) -> PsiVal {
        if !is_cons(cell) { return PSI_NIL; }
        self.cells[(cell & !PSI_CONS_TAG) as usize].0
    }

    #[inline]
    pub fn cdr(&self, cell: PsiVal) -> PsiVal {
        if !is_cons(cell) { return PSI_NIL; }
        self.cells[(cell & !PSI_CONS_TAG) as usize].1
    }
}

// ── Display ──────────────────────────────────────────────────────

pub fn psi_print_val(arena: &Arena, v: PsiVal) {
    if is_nil(v) { print!("NIL"); return; }
    if is_cons(v) {
        print!("(");
        psi_print_val(arena, arena.car(v));
        let mut rest = arena.cdr(v);
        while is_cons(rest) {
            print!(" ");
            psi_print_val(arena, arena.car(rest));
            rest = arena.cdr(rest);
        }
        if !is_nil(rest) {
            print!(" . ");
            psi_print_val(arena, rest);
        }
        print!(")");
        return;
    }
    print!("{}", v);
}

pub fn psi_println(arena: &Arena, v: PsiVal) {
    psi_print_val(arena, v);
    println!();
}

/// Print a cons-list of char codes as a string (for write-string with variable args).
pub fn psi_write_string(arena: &Arena, v: PsiVal) {
    let mut cur = v;
    while is_cons(cur) {
        let ch = arena.car(cur);
        if !is_nil(ch) && !is_cons(ch) {
            print!("{}", ch as u8 as char);
        }
        cur = arena.cdr(cur);
    }
}

// ── Atom names ──────────────────────────────────────────────────

static PSI_NAMES: [&str; 16] = [
    "TOP", "BOT", "f", "TAU", "g", "PHI", "Q", "E",
    "RHO", "ETA", "Y", "PSI", "CHI", "INC", "INV", "DEC",
];

/// Return atom name as a cons-list of ASCII char codes, or PSI_NIL for non-atoms.
pub fn psi_atom_name(arena: &mut Arena, v: PsiVal) -> PsiVal {
    if is_nil(v) || is_cons(v) { return PSI_NIL; }
    let idx = v as usize;
    let name = if idx < 16 { PSI_NAMES[idx] } else { return PSI_NIL; };
    let mut result = PSI_NIL;
    for &b in name.as_bytes().iter().rev() {
        result = arena.cons(b as PsiVal, result);
    }
    result
}
