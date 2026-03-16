/*
 * psi_runtime_c.h — Ψ₁₆ᶜ runtime for compiled Ψ∗ programs.
 *
 * C-interop-optimized variant of psi_runtime.h with:
 *   - INC/DEC/INV extension elements (indices 13, 14, 15)
 *   - Arithmetic inline helpers (no switch needed on core)
 *   - 5 supercompiler cancellation rules baked in
 *
 * Extension elements on core {2,3,4,5}:
 *   INC(x) = ((x - 1) & 3) + 2   (4-cycle: 2→3→4→5→2)
 *   DEC(x) = ((x - 3) & 3) + 2   (reverse:  2→5→4→3→2)
 *   INV(x) = 7 - x               (involution: 2↔5, 3↔4)
 */

#ifndef PSI_RUNTIME_C_H
#define PSI_RUNTIME_C_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ── Value representation ─────────────────────────────────────────── */

typedef int64_t psi_val;

#define PSI_NIL       INT64_MIN
#define PSI_CONS_TAG  (1LL << 62)
#define IS_NIL(x)     ((x) == PSI_NIL)
#define IS_CONS(x)    (((x) & PSI_CONS_TAG) && !IS_NIL(x))
#define IS_TRUE(x)    (!IS_NIL(x))

/* ── Cayley table (Ψ₁₆ᶜ) ────────────────────────────────────────── */

#define PSI_TOP  0
#define PSI_BOT  1
#define PSI_INC  13
#define PSI_INV  14
#define PSI_DEC  15

static const char *psi_names[16] = {
    "TOP", "BOT", "f", "tau", "g", "5", "Q", "E",
    "rho", "eta", "Y", "11", "SEQ", "INC", "INV", "DEC"
};

static const uint8_t psi_cayley[16][16] = {
    { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
    { 1, 4, 7, 3,12, 5, 9,15,10,15,13,11, 3, 8,14, 2},
    { 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
    {10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10},
    { 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0},
    { 1, 8,11,15,10, 6, 4,13, 7, 4,12,14, 3, 5, 9, 2},
    { 0, 1,15,12, 6,13, 5,11,14, 8, 4, 2, 7, 7, 6, 3},
    { 7, 1,10, 3,12, 5,12,14, 2, 4,11,13, 8, 6,14, 9},
    { 4, 1,11,11,11,11, 4, 5, 3, 6, 2,10, 7, 3,13, 9},
    { 1, 8, 2,13,10, 7, 7,12, 5, 9,14, 3,15, 4, 6,11},
    { 1, 6, 3, 3, 7, 3,11, 2,11, 4, 8,13, 5,11,11, 3},
    { 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
    { 1, 2, 3, 4, 5, 2,14, 5,12, 3,13,11,13,15,15, 5},
    { 1, 0, 5, 4, 3, 2,10, 9,14, 7, 6,12,11,13, 8,15},
    { 0, 3, 5, 2, 3, 4, 3, 3, 5,13,13, 4,12, 5,15,14},
};

static inline uint8_t psi_dot(uint8_t a, uint8_t b) {
    return psi_cayley[a][b];
}

/* ── Arithmetic helpers for INC/DEC/INV on core {2,3,4,5} ────────── */
/* These are single arithmetic expressions — gcc optimizes them well.  */
/* For non-core arguments, fall back to the Cayley table.              */

static inline uint8_t psi_inc(uint8_t x) {
    /* 4-cycle: 2→3→4→5→2. Arithmetic: ((x-1) & 3) + 2 */
    if (x >= 2 && x <= 5) return ((x - 1) & 3) + 2;
    return psi_cayley[PSI_INC][x];
}

static inline uint8_t psi_dec(uint8_t x) {
    /* Reverse: 2→5→4→3→2. Arithmetic: ((x-3) & 3) + 2 */
    if (x >= 2 && x <= 5) return ((x - 3) & 3) + 2;
    return psi_cayley[PSI_DEC][x];
}

static inline uint8_t psi_inv(uint8_t x) {
    /* Involution: 2↔5, 3↔4. Arithmetic: 7-x */
    if (x >= 2 && x <= 5) return 7 - x;
    return psi_cayley[PSI_INV][x];
}

/* ── Cons cell arena ──────────────────────────────────────────────── */
/* Note: C runtime uses a bump allocator with no garbage collection.   */
/* Suitable for benchmarks and short-lived programs.                    */
/* For long-running programs, use the Rust backend (--target rust)     */
/* which will integrate MMTk GC in a future release.                   */

#define PSI_HEAP_SIZE 1000000

static struct { psi_val car, cdr; } psi_heap[PSI_HEAP_SIZE];
static int psi_hp = 0;

static inline psi_val psi_cons(psi_val car, psi_val cdr) {
    if (psi_hp >= PSI_HEAP_SIZE) {
        fprintf(stderr, "psi: heap overflow\n");
        exit(1);
    }
    int idx = psi_hp++;
    psi_heap[idx].car = car;
    psi_heap[idx].cdr = cdr;
    return PSI_CONS_TAG | idx;
}

static inline psi_val psi_car(psi_val cell) {
    if (!IS_CONS(cell)) return PSI_NIL;
    return psi_heap[cell & ~PSI_CONS_TAG].car;
}

static inline psi_val psi_cdr(psi_val cell) {
    if (!IS_CONS(cell)) return PSI_NIL;
    return psi_heap[cell & ~PSI_CONS_TAG].cdr;
}

/* ── Display ──────────────────────────────────────────────────────── */

static void psi_print_val(psi_val v) {
    if (IS_NIL(v)) { printf("NIL"); return; }
    if (IS_CONS(v)) {
        printf("(");
        psi_print_val(psi_car(v));
        psi_val rest = psi_cdr(v);
        while (IS_CONS(rest)) {
            printf(" ");
            psi_print_val(psi_car(rest));
            rest = psi_cdr(rest);
        }
        if (!IS_NIL(rest)) {
            printf(" . ");
            psi_print_val(rest);
        }
        printf(")");
        return;
    }
    printf("%lld", (long long)v);
}

static void psi_println(psi_val v) {
    psi_print_val(v);
    printf("\n");
}

#endif /* PSI_RUNTIME_C_H */
