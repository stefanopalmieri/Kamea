//! Stress test for wispy-gc: 10M cons cells, only 1000 live at a time.
//!
//! With the bump allocator, this would OOM (10M * 24 bytes = 240MB).
//! With MMTk GC and a small heap (e.g., 4MB), intermediate lists should
//! be collected and the program should complete in constant heap space.

use wispy_gc::*;

/// Build a list of n cons cells: (n . (n-1 . (... . (1 . NIL))))
fn make_list(n: i64) -> WispyVal {
    let mut result = WISPY_NIL;
    for i in 1..=n {
        // Shadow-stack protect `result` across allocation.
        let idx = shadow_push(result);
        result = wispy_cons(i, shadow_get(idx));
        shadow_pop(1);
    }
    result
}

/// Sum all car values in a list.
fn sum_list(mut lst: WispyVal) -> i64 {
    let mut total: i64 = 0;
    while is_cons(lst) {
        total += wispy_car(lst);
        lst = wispy_cdr(lst);
    }
    total
}


fn main() {
    let iterations = 10_000;
    let list_size = 1_000;
    // Expected sum of 1..1000 = 500500
    let expected_per_list: i64 = list_size * (list_size + 1) / 2;
    let expected_total: i64 = expected_per_list * iterations;

    // Start with 256 MB to test allocation path, then shrink to test GC.
    let heap_mb = std::env::var("HEAP_MB").ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(256);
    let heap_bytes = heap_mb * 1024 * 1024;

    println!("wispy-gc stress test");
    println!("  {} iterations × {} cons cells = {} total allocations",
             iterations, list_size, iterations * list_size);
    println!("  Heap: {} MB (would need ~240 MB without GC)", heap_mb);
    println!("  Expected total: {}", expected_total);

    wispy_init_with_heap(heap_bytes);

    let mut total: i64 = 0;
    for i in 0..iterations {
        let lst = make_list(list_size);
        total += sum_list(lst);
        // `lst` is now dead — GC can reclaim it.
        if (i + 1) % 1000 == 0 {
            print!("  [{}/{}] total so far: {}\r", i + 1, iterations, total);
        }
    }
    println!();

    if total == expected_total {
        println!("  PASS: total = {} (expected {})", total, expected_total);
    } else {
        println!("  FAIL: total = {} (expected {})", total, expected_total);
        std::process::exit(1);
    }

    wispy_shutdown();
    println!("  Stress test complete.");
}
