//! N-Queens(8) and counter arithmetic benchmarks using MMTk GC.
//!
//! Same algorithms as benchmarks/bench_nqueens_runtime.c and
//! benchmarks/bench_counter_runtime.c, but cons cells are GC-managed.
//!
//! Run: HEAP_MB=32 cargo run -p wispy-bench --release -- 8

use wispy_gc::*;
use std::time::Instant;

// --- N-Queens ---

fn abs_diff(a: i64, b: i64) -> i64 {
    if a > b { a - b } else { b - a }
}

fn safe_p(queen: i64, dist: i64, placed: WispyVal) -> bool {
    if is_nil(placed) {
        return true;
    }
    let q = wispy_car(placed);
    if queen == q {
        return false;
    }
    if abs_diff(queen, q) == dist {
        return false;
    }
    let rest = wispy_cdr(placed);
    safe_p(queen, dist + 1, rest)
}

fn nqueens_count(n: i64, row: i64, placed: WispyVal) -> i64 {
    if row == n {
        return 1;
    }
    count_cols(n, 0, row, placed)
}

fn count_cols(n: i64, col: i64, row: i64, placed: WispyVal) -> i64 {
    if col == n {
        return 0;
    }
    let s = if safe_p(col, 1, placed) {
        // Protect `placed` across allocation
        let idx = shadow_push(placed);
        let new_placed = wispy_cons(col, shadow_get(idx));
        shadow_pop(1);
        nqueens_count(n, row + 1, new_placed)
    } else {
        0
    };
    s + count_cols(n, col + 1, row, placed)
}

fn nqueens(n: i64) -> i64 {
    nqueens_count(n, 0, WISPY_NIL)
}

// --- Counter arithmetic ---

fn fib(n: i64) -> i64 {
    if n < 2 { n } else { fib(n - 1) + fib(n - 2) }
}

fn fib_iter(n: i64) -> i64 {
    let (mut a, mut b) = (0i64, 1i64);
    for _ in 0..n {
        let t = a + b;
        a = b;
        b = t;
    }
    a
}

fn fact(n: i64) -> i64 {
    if n == 0 { 1 } else { n * fact(n - 1) }
}

fn power(base: i64, exp: i64) -> i64 {
    if exp == 0 { 1 } else { base * power(base, exp - 1) }
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn counter_arith() -> i64 {
    fib(8) + fib_iter(30) + fact(10) + power(2, 10) + gcd(100, 75)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: i64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(8);

    let heap_mb = std::env::var("HEAP_MB").ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(32);

    wispy_init_with_heap(heap_mb * 1024 * 1024);

    // --- Counter arithmetic benchmark ---
    let iters = 1_000_000;
    // Warmup
    counter_arith();

    let t0 = Instant::now();
    let mut result = 0i64;
    for _ in 0..iters {
        result = counter_arith();
    }
    let elapsed = t0.elapsed();
    let per_iter_us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    println!("Counter arithmetic: {:.3} µs/iter ({} iters, result={})",
             per_iter_us, iters, result);

    // --- N-Queens benchmark ---
    let nq_iters = 10_000;
    // Warmup
    nqueens(n);

    let t0 = Instant::now();
    let mut nq_result = 0i64;
    for _ in 0..nq_iters {
        nq_result = nqueens(n);
    }
    let elapsed = t0.elapsed();
    let per_iter_us = elapsed.as_secs_f64() / nq_iters as f64 * 1e6;
    println!("N-Queens({}):        {:.1} µs/iter ({} iters, result={})",
             n, per_iter_us, nq_iters, nq_result);

    wispy_shutdown();
}
