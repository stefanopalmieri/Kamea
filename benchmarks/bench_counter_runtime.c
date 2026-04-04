/* bench_counter_runtime.c — C baseline with argv inputs (no constant folding)
 * Compile: gcc -O2 -o bench_counter_runtime benchmarks/bench_counter_runtime.c
 * Run:     ./bench_counter_runtime 8 30 10 2 10 100 75
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

typedef int64_t val;

static val fib(val n) {
    if (n < 2) return n;
    return fib(n - 1) + fib(n - 2);
}

static val fib_iter(val n) {
    val a = 0, b = 1;
    for (val i = 0; i < n; i++) {
        val t = a + b;
        a = b;
        b = t;
    }
    return a;
}

static val fact(val n) {
    if (n == 0) return 1;
    return n * fact(n - 1);
}

static val my_power(val base, val exp) {
    if (exp == 0) return 1;
    return base * my_power(base, exp - 1);
}

static val my_gcd(val a, val b) {
    if (b == 0) return a;
    return my_gcd(b, a % b);
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "Usage: %s fib_n iter_n fact_n pow_base pow_exp gcd_a gcd_b\n", argv[0]);
        return 1;
    }
    val fib_n    = atoi(argv[1]);
    val iter_n   = atoi(argv[2]);
    val fact_n   = atoi(argv[3]);
    val pow_base = atoi(argv[4]);
    val pow_exp  = atoi(argv[5]);
    val gcd_a    = atoi(argv[6]);
    val gcd_b    = atoi(argv[7]);

    int iters = 1000000;
    volatile val result = 0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < iters; i++) {
        result = fib(fib_n) + fib_iter(iter_n) + fact(fact_n) +
                 my_power(pow_base, pow_exp) + my_gcd(gcd_a, gcd_b);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);

    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
    double per_iter_us = elapsed / iters * 1e6;

    printf("Counter arithmetic: %.3f µs/iter (%d iters, result=%lld)\n",
           per_iter_us, iters, (long long)result);
    return 0;
}
