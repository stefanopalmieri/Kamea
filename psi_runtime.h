/*
 * psi_runtime.h — Ψ₁₆ᶠ runtime for compiled Ψ∗ programs.
 *
 * Two layers:
 *   1. Cayley table (256 bytes) — the finite algebra
 *   2. Cons cells (arena) — the term algebra (lists, pairs)
 *
 * Generated from the Lean-verified Cayley table (DiscoverableKamea.lean).
 */

#ifndef PSI_RUNTIME_H
#define PSI_RUNTIME_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ── Value representation ─────────────────────────────────────────── */
/* All values are int64_t. Numbers are plain integers.                */
/* NIL is a special sentinel. Cons cells use a tag bit.               */

typedef int64_t psi_val;

#define PSI_NIL       INT64_MIN
#define PSI_CONS_TAG  (1LL << 62)
#define IS_NIL(x)     ((x) == PSI_NIL)
#define IS_CONS(x)    (((x) & PSI_CONS_TAG) && !IS_NIL(x))
/* Truthy: everything except NIL */
#define IS_TRUE(x)    (!IS_NIL(x))

/* ── Cayley table ─────────────────────────────────────────────────── */

#define PSI_TOP  0
#define PSI_BOT  1

static const char *psi_names[16] = {
    "TOP", "BOT", "f", "tau", "g", "SEQ", "Q", "E",
    "rho", "eta", "Y", "PAIR", "s0", "INC", "GET", "DEC"
};

static const uint8_t psi_cayley[16][16] = {
    { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
    { 5, 1,13, 7,11, 5, 6, 8, 2, 5,11, 9, 4,14, 3,15},
    { 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1},
    { 0,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11},
    { 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0},
    {15, 0, 5, 9, 3,15,14,14, 2,12, 8,14,12, 4,12, 8},
    { 0, 1, 8, 4,13, 2,11, 2,14, 3,15,12,14,15, 6, 5},
    {12, 1,13, 7,11, 5,12,11, 4,12, 5,14,15, 7,11,12},
    { 1, 6,14,14,14,14, 9, 8, 3,15, 5, 7,13,11,12, 4},
    {13, 1, 4, 3,12,11, 2,11, 5, 3, 8,14, 9, 7,11,11},
    {14, 1, 9,10,11,13,12, 7, 5, 6, 8, 2,14,12,10, 4},
    { 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1},
    { 3, 0,14, 4,14, 6,11,12, 7, 3,15,10,14, 2, 6, 8},
    {14, 0, 5, 4, 3, 2,12, 5,11,14, 3,14,12, 2, 6, 3},
    { 1, 3,13,15, 3, 7,14, 8,15, 4,11, 6, 7,14,12,10},
};

static inline uint8_t psi_dot(uint8_t a, uint8_t b) {
    return psi_cayley[a][b];
}

/* ── Cons cell arena ──────────────────────────────────────────────── */

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

#endif /* PSI_RUNTIME_H */
