use psi_runtime::io::BufferIo;
use psi_runtime::machine::{Machine, Value, VOID_TERM};

// The Ψ-Lisp evaluator uses Rust recursion (the machine level),
// so deep Lisp recursion needs adequate stack. In debug mode, Rust
// frames are large, so we increase the default test thread stack.
const STACK_SIZE: usize = 16 * 1024 * 1024; // 16 MB

fn run_lisp(source: &str) -> (Vec<String>, String) {
    let mut machine = Machine::new(BufferIo::new());
    let results = machine.run(source).expect("run failed");
    let mut display_results = Vec::new();
    for r in results {
        if let Value::Term(t) = r {
            if t != VOID_TERM {
                display_results.push(machine.display(t));
            }
        }
    }
    let io_output = String::from_utf8(machine.io.output.clone()).unwrap_or_default();
    (display_results, io_output)
}

fn assert_results(source: &str, expected: &[&str]) {
    let (results, _) = run_lisp(source);
    assert_eq!(
        results, expected,
        "source: {}\nexpected: {:?}\ngot: {:?}",
        source, expected, results
    );
}

#[test]
fn test_basic_atoms() {
    assert_results("42", &["42"]);
    assert_results("0", &["0"]);
    assert_results("T", &["T"]);
    assert_results("NIL", &["NIL"]);
}

#[test]
fn test_arithmetic() {
    assert_results("(+ 3 4)", &["7"]);
    assert_results("(- 10 3)", &["7"]);
    assert_results("(* 4 5)", &["20"]);
    assert_results("(+ (* 3 4) (* 5 6))", &["42"]);
    assert_results("(mod 17 5)", &["2"]);
}

#[test]
fn test_comparison() {
    assert_results("(< 3 5)", &["T"]);
    assert_results("(> 3 5)", &["NIL"]);
    assert_results("(= 7 7)", &["T"]);
    assert_results("(= 7 8)", &["NIL"]);
}

#[test]
fn test_list_operations() {
    assert_results("(cons 1 (cons 2 (cons 3 NIL)))", &["(1 2 3)"]);
    assert_results("(car (cons 10 (cons 20 NIL)))", &["10"]);
    assert_results("(cdr (cons 10 (cons 20 NIL)))", &["(20)"]);
    assert_results("(list 1 2 3 4 5)", &["(1 2 3 4 5)"]);
}

#[test]
fn test_quote() {
    assert_results("(quote (1 2 3))", &["(1 2 3)"]);
    assert_results("'(1 2 3)", &["(1 2 3)"]);
}

#[test]
fn test_if() {
    assert_results("(if T 1 2)", &["1"]);
    assert_results("(if NIL 1 2)", &["2"]);
    assert_results("(if 0 1 2)", &["1"]); // 0 is truthy
}

#[test]
fn test_defun() {
    assert_results(
        "(defun square (x) (* x x)) (square 5)",
        &["25"],
    );
}

#[test]
fn test_lambda() {
    assert_results("((lambda (x) (+ x 1)) 10)", &["11"]);
}

#[test]
fn test_let() {
    assert_results("(let ((x 5) (y 3)) (+ x y))", &["8"]);
}

#[test]
fn test_recursion() {
    assert_results(
        "(defun fact (n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5)",
        &["120"],
    );
}

#[test]
fn test_fibonacci() {
    assert_results(
        "(defun fib (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) (fib 10)",
        &["55"],
    );
}

#[test]
fn test_higher_order() {
    assert_results(
        "(defun mapcar (f lst) (if (null lst) NIL (cons (f (car lst)) (mapcar f (cdr lst))))) \
         (mapcar (lambda (x) (+ x 1)) (list 1 2 3))",
        &["(2 3 4)"],
    );
}

#[test]
fn test_null_zerop() {
    assert_results("(null NIL)", &["T"]);
    assert_results("(null 0)", &["NIL"]);
    assert_results("(zerop 0)", &["T"]);
    assert_results("(zerop 1)", &["NIL"]);
    assert_results("(zerop NIL)", &["NIL"]);
}

#[test]
fn test_write_char_io() {
    let (results, io) = run_lisp("(write-char 72)(write-char 105)");
    assert_eq!(io, "Hi");
}

#[test]
fn test_write_string_io() {
    let (_, io) = run_lisp(r#"(write-string "Hi\n")"#);
    assert_eq!(io, "Hi\n");
}

#[test]
fn test_setq_lambda() {
    assert_results(
        "(setq double (lambda (x) (* x 2))) (double 7)",
        &["14"],
    );
}

#[test]
fn test_compose() {
    assert_results(
        "(defun compose (f g) (lambda (x) (f (g x)))) \
         (setq add1 (lambda (x) (+ x 1))) \
         (setq dbl (lambda (x) (* x 2))) \
         (setq dbl-then-add1 (compose add1 dbl)) \
         (dbl-then-add1 5)",
        &["11"],
    );
}

#[test]
fn test_reduce() {
    assert_results(
        "(defun reduce (f acc lst) (if (null lst) acc (reduce f (f acc (car lst)) (cdr lst)))) \
         (reduce + 0 (list 1 2 3 4 5))",
        &["15"],
    );
}

#[test]
fn test_full_basic_example() {
    let source = std::fs::read_to_string("../../examples/psi_basic.lisp").unwrap();
    let (results, _) = run_lisp(&source);
    let expected = vec![
        "42", "0", "T", "NIL", "100", "(1 2 3)", "(1 2 3)",
        "10", "(20)", "((1 . 2) . (3 . 4))", "(1 2 3 4 5)",
    ];
    assert_eq!(results, expected);
}

#[test]
fn test_full_arithmetic_example() {
    let source = std::fs::read_to_string("../../examples/psi_arithmetic.lisp").unwrap();
    let (results, _) = run_lisp(&source);
    let expected = vec!["7", "7", "20", "T", "NIL", "T", "NIL", "T", "NIL", "42", "99", "2", "1"];
    assert_eq!(results, expected);
}

/// Helper to run tests that need deep Lisp recursion on a larger stack.
fn run_on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    let builder = std::thread::Builder::new().stack_size(STACK_SIZE);
    let handle = builder.spawn(f).unwrap();
    handle.join().unwrap();
}

#[test]
fn test_full_recursion_example() {
    run_on_big_stack(|| {
        let source = std::fs::read_to_string("../../examples/psi_recursion.lisp").unwrap();
        let (results, _) = run_lisp(&source);
        let expected = vec!["1", "1", "120", "3628800", "55", "5050", "1024", "243", "4", "25"];
        assert_eq!(results, expected);
    });
}

#[test]
fn test_full_fibonacci_example() {
    run_on_big_stack(|| {
        let source = std::fs::read_to_string("../../examples/psi_fibonacci.lisp").unwrap();
        let (results, _) = run_lisp(&source);
        let expected = vec![
            "0", "1", "1", "2", "5", "21", "55",
            "55", "6765", "832040",
            "(0 1 1 2 3 5 8 13 21 34)",
        ];
        assert_eq!(results, expected);
    });
}

#[test]
fn test_full_higher_example() {
    run_on_big_stack(|| {
        let source = std::fs::read_to_string("../../examples/psi_higher.lisp").unwrap();
        let (results, _) = run_lisp(&source);
        let expected = vec![
            "(2 3 4)", "(1 4 9 16 25)", "(2 4 6 8 10)",
            "15", "120", "3", "0", "(1 2 3 4 5 6)", "(5 4 3 2 1)",
        ];
        assert_eq!(results, expected);
    });
}
