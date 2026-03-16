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

    // Extract --table=c flag from anywhere in the args
    let use_table_c = args.iter().any(|a| a == "--table=c");
    let args: Vec<&String> = args.iter().filter(|a| a.as_str() != "--table=c").collect();

    if args.len() < 2 {
        repl(use_table_c);
        return;
    }

    match args[1].as_str() {
        "run" => {
            if args.len() < 3 {
                eprintln!("Usage: kamea [--table=c] run <file.lisp> [file2.lisp ...]");
                std::process::exit(1);
            }
            let paths: Vec<String> = args[2..].iter().map(|s| s.to_string()).collect();
            run_files(&paths, use_table_c);
        }
        "repl" => repl(use_table_c),
        "bench" => {
            if args.len() < 3 {
                eprintln!("Usage: kamea [--table=c] bench <file.lisp>");
                std::process::exit(1);
            }
            bench_file(args[2], use_table_c);
        }
        path if path.ends_with(".lisp") => {
            let paths: Vec<String> = args[1..].iter().map(|s| s.to_string()).collect();
            run_files(&paths, use_table_c);
        }
        _ => {
            eprintln!("Usage: kamea [--table=c] [run|repl|bench] [file.lisp]");
            std::process::exit(1);
        }
    }
}

fn make_machine(use_table_c: bool) -> Machine<StdIo> {
    if use_table_c {
        Machine::new_c(StdIo)
    } else {
        Machine::new(StdIo)
    }
}

fn run_files(paths: &[String], use_table_c: bool) {
    let mut machine = make_machine(use_table_c);
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

fn bench_file(path: &str, use_table_c: bool) {
    let source = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", path, e);
        std::process::exit(1);
    });

    let start = std::time::Instant::now();
    let mut machine = make_machine(use_table_c);
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

fn repl(use_table_c: bool) {
    let mut machine = make_machine(use_table_c);
    let table_name = if use_table_c { "Ψ₁₆ᶜ" } else { "Ψ₁₆ᶠ" };
    println!("Ψ∗ Mini-Lisp ({}) — type expressions, Ctrl-D to exit", table_name);
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
