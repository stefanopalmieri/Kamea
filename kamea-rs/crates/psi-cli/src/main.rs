use psi_runtime::io::StdIo;
use psi_runtime::machine::{Machine, Value, VOID_TERM};
use std::io::{self, BufRead, Write};

fn main() {
    // The metacircular evaluator (Lisp-in-Lisp) creates deep call stacks.
    // Default 8MB is insufficient; use 64MB.
    let stack_size = 64 * 1024 * 1024;
    let builder = std::thread::Builder::new().stack_size(stack_size);
    let handler = builder.spawn(|| { real_main(); }).unwrap();
    handler.join().unwrap();
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        repl();
        return;
    }

    match args[1].as_str() {
        "run" => {
            if args.len() < 3 {
                eprintln!("Usage: kamea run <file.lisp> [file2.lisp ...]");
                std::process::exit(1);
            }
            run_files(&args[2..]);
        }
        "repl" => repl(),
        "bench" => {
            if args.len() < 3 {
                eprintln!("Usage: kamea bench <file.lisp>");
                std::process::exit(1);
            }
            bench_file(&args[2]);
        }
        path if path.ends_with(".lisp") => {
            run_files(&args[1..]);
        }
        _ => {
            eprintln!("Usage: kamea [run|repl|bench] [file.lisp]");
            std::process::exit(1);
        }
    }
}

fn run_files(paths: &[String]) {
    let mut machine = Machine::new(StdIo);
    for path in paths {
        let source = std::fs::read_to_string(path).unwrap_or_else(|e| {
            eprintln!("Error reading {}: {}", path, e);
            std::process::exit(1);
        });

        println!("── {} ──", path);

        match machine.run(&source) {
            Ok(results) => {
                for r in results {
                    if let Value::Term(t) = r {
                        if t != VOID_TERM {
                            println!("{}", machine.display(t));
                        }
                    }
                }
            }
            Err(e) => {
                eprintln!("error: {}", e);
                std::process::exit(1);
            }
        }
        println!();
    }
}

fn bench_file(path: &str) {
    let source = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", path, e);
        std::process::exit(1);
    });

    let start = std::time::Instant::now();
    let mut machine = Machine::new(StdIo);
    match machine.run_and_print(&source) {
        Ok(()) => {
            let elapsed = start.elapsed();
            let stats = machine.stats();
            println!("\n--- Benchmark ---");
            println!("Time: {:.3}s", elapsed.as_secs_f64());
            println!("Arena: {} nodes", stats.arena_size);
        }
        Err(e) => {
            eprintln!("error: {}", e);
            std::process::exit(1);
        }
    }
}

fn repl() {
    let mut machine = Machine::new(StdIo);
    println!("Ψ∗ Mini-Lisp — type expressions, Ctrl-D to exit");
    println!("  T = ⊤ (true), NIL = ⊥ (false/empty list)");
    println!("  Integers = Q-chains rooted at ⊤. Only NIL is falsy.");
    println!();

    let stdin = io::stdin();
    loop {
        print!("ψ> ");
        io::stdout().flush().unwrap();

        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => {
                println!();
                break;
            }
            Ok(_) => {}
            Err(_) => break,
        }

        let line = line.trim().to_string();
        if line.is_empty() {
            continue;
        }

        match machine.run(&line) {
            Ok(results) => {
                for r in results {
                    if let Value::Term(t) = r {
                        if t != VOID_TERM {
                            println!("{}", machine.display(t));
                        }
                    }
                }
            }
            Err(e) => eprintln!("error: {}", e),
        }
    }
}
