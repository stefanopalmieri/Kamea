/*
 * psi_runtime.h — Ψ₁₆ᶠ Cayley table runtime for compiled Ψ∗ programs.
 *
 * The entire algebra is a 256-byte lookup table. psi_dot(a, b) is a
 * single array access. With -O2, gcc inlines it completely.
 *
 * Generated from the Lean-verified Cayley table (DiscoverableKamea.lean).
 */

#ifndef PSI_RUNTIME_H
#define PSI_RUNTIME_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* Named atoms */
#define PSI_TOP  0
#define PSI_BOT  1
#define PSI_F    2
#define PSI_TAU  3
#define PSI_G    4
#define PSI_SEQ  5
#define PSI_Q    6
#define PSI_E    7
#define PSI_RHO  8
#define PSI_ETA  9
#define PSI_Y   10
#define PSI_PAIR 11
#define PSI_S0  12
#define PSI_INC 13
#define PSI_GET 14
#define PSI_DEC 15

static const char *psi_names[16] = {
    "TOP", "BOT", "f", "tau", "g", "SEQ", "Q", "E",
    "rho", "eta", "Y", "PAIR", "s0", "INC", "GET", "DEC"
};

/* The 16x16 Cayley table — 256 bytes, the entire algebra. */
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

#endif /* PSI_RUNTIME_H */
