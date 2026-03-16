// psi_runtime.rs — Ψ₁₆ᶜ runtime for compiled Ψ∗ programs (Rust).
//
// Two layers:
//   1. Cayley table (256 bytes) — the finite algebra
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

// ── Cayley table (Ψ₁₆ᶜ) ────────────────────────────────────────

pub const PSI_TOP: u8 = 0;
pub const PSI_BOT: u8 = 1;
pub const PSI_INC: u8 = 13;
pub const PSI_INV: u8 = 14;
pub const PSI_DEC: u8 = 15;

pub static PSI_CAYLEY: [[u8; 16]; 16] = [
    [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [ 1, 4, 7, 3,12, 5, 9,15,10,15,13,11, 3, 8,14, 2],
    [ 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],
    [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [ 1, 8,11,15,10, 6, 4,13, 7, 4,12,14, 3, 5, 9, 2],
    [ 0, 1,15,12, 6,13, 5,11,14, 8, 4, 2, 7, 7, 6, 3],
    [ 7, 1,10, 3,12, 5,12,14, 2, 4,11,13, 8, 6,14, 9],
    [ 4, 1,11,11,11,11, 4, 5, 3, 6, 2,10, 7, 3,13, 9],
    [ 1, 8, 2,13,10, 7, 7,12, 5, 9,14, 3,15, 4, 6,11],
    [ 1, 6, 3, 3, 7, 3,11, 2,11, 4, 8,13, 5,11,11, 3],
    [ 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [ 1, 2, 3, 4, 5, 2,14, 5,12, 3,13,11,13,15,15, 5],
    [ 1, 0, 5, 4, 3, 2,10, 9,14, 7, 6,12,11,13, 8,15],
    [ 0, 3, 5, 2, 3, 4, 3, 3, 5,13,13, 4,12, 5,15,14],
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
