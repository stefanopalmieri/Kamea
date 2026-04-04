/* bench_nqueens_runtime.c — C baseline N-Queens with argv input
 * Compile: gcc -O2 -o bench_nqueens_c benchmarks/bench_nqueens_runtime.c
 * Run:     ./bench_nqueens_c 8
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

/* Cons-cell arena (bump allocator, like Psi-Lisp runtime) */
#define HEAP_SIZE 2000000
static struct { int car; int next; } heap[HEAP_SIZE];
static int hp = 0;

static inline int cons(int x, int lst) {
    int idx = hp++;
    heap[idx].car = x;
    heap[idx].next = lst;
    return idx + 1; /* 0 = nil */
}

static inline int car(int lst) { return heap[lst - 1].car; }
static inline int cdr(int lst) { return heap[lst - 1].next; }

static int abs_diff(int a, int b) { return a > b ? a - b : b - a; }

static int safe_p(int queen, int dist, int placed) {
    if (placed == 0) return 1;
    int q = car(placed);
    if (queen == q) return 0;
    if (abs_diff(queen, q) == dist) return 0;
    return safe_p(queen, dist + 1, cdr(placed));
}

static int nqueens_count(int n, int row, int placed);

static int count_cols(int n, int col, int row, int placed) {
    if (col == n) return 0;
    int s = 0;
    if (safe_p(col, 1, placed))
        s = nqueens_count(n, row + 1, cons(col, placed));
    return s + count_cols(n, col + 1, row, placed);
}

static int nqueens_count(int n, int row, int placed) {
    if (row == n) return 1;
    return count_cols(n, 0, row, placed);
}

static int nqueens(int n) {
    hp = 0;
    return nqueens_count(n, 0, 0);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "Usage: %s N\n", argv[0]); return 1; }
    int n = atoi(argv[1]);

    /* Warmup */
    nqueens(n);

    int iters = 10000;
    struct timespec t0, t1;
    volatile int result = 0;

    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < iters; i++) {
        result = nqueens(n);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);

    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
    double per_iter_us = elapsed / iters * 1e6;
    printf("N-Queens(%d):        %.1f µs/iter (%d iters, result=%d)\n",
           n, per_iter_us, iters, result);
    return 0;
}
