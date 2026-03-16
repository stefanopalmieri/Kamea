# Build: Meta-Circular CPS Evaluator for Ψ-Lisp

## The Big Idea

A continuation-passing style meta-circular interpreter is a state machine. The Kamea evaluator is already a state machine. Write the Ψ-Lisp evaluator IN Ψ-Lisp, in CPS, and reify/reflect become trivial — the continuation is just a Ψ∗ term sitting in a variable, not something trapped in the Python call stack.

This is the classical technique. See:
- Reynolds, "Definitional Interpreters for Higher-Order Programming Languages" (1972)
- Steele & Sussman, "The Scheme-79 Chip" — CPS interpreter as hardware state machine
- Smith, "Reflection and Semantics in Lisp" (1984) — 3-Lisp reflective tower
- Reference implementation: https://github.com/nikitadanilov/3-lisp

The key passage from that repo's README:

> "continuation passing style can be understood as a mechanism that makes meta-circular interpretation independent of the evaluation strategy... As a by-product, a continuation passing style interpreter is essentially a state machine and so can be implemented in hardware"

That's us. We're building toward hardware. The CPS evaluator IS the machine specification.

## What to Build

### A meta-circular Ψ-Lisp evaluator written in Ψ-Lisp

A file `examples/psi_metacircular.lisp` (or `psi_tower.lisp`) that implements `eval` and `apply` as Ψ-Lisp functions operating on Ψ∗ terms, with explicit continuations.

Study the 3-Lisp source at https://github.com/nikitadanilov/3-lisp carefully. Understand its structure. The key components are:

1. **Explicit continuations.** Every evaluation step takes a continuation argument `k` — a function that receives the result and does the next thing. Instead of `(eval expr env) → value`, you have `(eval expr env k)` where `k` is called with the result.

2. **Environment as data.** The environment is an association list — already how Ψ-Lisp works. No change needed.

3. **Reify as continuation capture.** `(reify)` grabs the current continuation `k` and passes it to the program as a first-class value. Since `k` is a Ψ∗ term (a lambda), the program can inspect it with `car`/`cdr` if it's a closure, or just call it.

4. **Reflect as continuation installation.** `(reflect value k)` abandons the current continuation and jumps to `k` with `value`. The program resumes in a different future.

### The structure (borrowing from 3-Lisp architecture)

```lisp
;;;; psi_metacircular.lisp — CPS Meta-Circular Evaluator
;;;;
;;;; A Ψ-Lisp interpreter written in Ψ-Lisp with explicit
;;;; continuations. Reify/reflect are natural operations on
;;;; the continuation, not special builtins.

;;; ── Continuation constructors ───────────────────────

;; A continuation is just a lambda that takes one argument (the result).
;; (make-cont (lambda (val) ...do-next...))

;;; ── The evaluator ───────────────────────────────────

(defun meta-eval (expr env k)
  "Evaluate expr in env, passing result to continuation k."
  (cond
    ;; Self-evaluating: numbers, T, NIL
    ((numberp expr)  (k expr))
    ((null expr)     (k NIL))
    ((eq expr T)     (k T))

    ;; Variable lookup
    ((symbolp expr)  (k (lookup expr env)))

    ;; Special forms
    ((eq (car expr) 'quote)
     (k (car (cdr expr))))

    ((eq (car expr) 'if)
     (meta-eval (car (cdr expr)) env
       (lambda (test-val)
         (if test-val
           (meta-eval (car (cdr (cdr expr))) env k)
           (meta-eval (car (cdr (cdr (cdr expr)))) env k)))))

    ((eq (car expr) 'lambda)
     (k (make-closure (car (cdr expr))         ;; params
                      (car (cdr (cdr expr)))   ;; body
                      env)))

    ((eq (car expr) 'defun)
     ... )

    ;; REIFY — the 3-Lisp move
    ;; Captures the current continuation and environment
    ;; as a first-class value
    ((eq (car expr) 'reify)
     (k (list (cons 'continuation k)
              (cons 'environment env)
              (cons 'expression expr))))

    ;; REFLECT — resume with a (possibly modified) state
    ((eq (car expr) 'reflect)
     (meta-eval (car (cdr expr)) env
       (lambda (state)
         (let ((new-k   (cdr (assoc 'continuation state)))
               (new-env (cdr (assoc 'environment state))))
           ;; Jump to the captured/modified continuation
           ;; This abandons the CURRENT continuation
           (meta-eval (car (cdr (cdr expr))) new-env new-k)))))

    ;; Function application
    (t
     (meta-eval (car expr) env
       (lambda (fn)
         (eval-args (cdr expr) env
           (lambda (args)
             (meta-apply fn args k))))))))

(defun meta-apply (fn args k)
  "Apply fn to args, passing result to continuation k."
  (cond
    ((closurep fn)
     (meta-eval (closure-body fn)
                (extend-env (closure-params fn) args (closure-env fn))
                k))
    ((builtinp fn)
     (k (apply-builtin fn args)))
    (t (error "not a function"))))

(defun eval-args (arg-exprs env k)
  "Evaluate a list of argument expressions, passing results list to k."
  (if (null arg-exprs)
    (k NIL)
    (meta-eval (car arg-exprs) env
      (lambda (val)
        (eval-args (cdr arg-exprs) env
          (lambda (rest)
            (k (cons val rest))))))))
```

### Reify/Reflect — how they work

**Reify** is not a builtin. It's a case in `meta-eval`. When the evaluator encounters `(reify)`, it packages the current continuation `k` and environment `env` into a normal Lisp data structure and passes that to `k`. The program receives its own future as data.

**Reflect** is also a case in `meta-eval`. When the evaluator encounters `(reflect state value)`, it extracts the continuation and environment from `state`, and calls the extracted continuation with `value`. The current continuation is abandoned. The program jumps to a different future — possibly one it has modified.

This is exactly how 3-Lisp works, adapted to Ψ-Lisp's semantics.

### The demo: three levels for real

```lisp
;;;; psi_reflective_tower.lisp — using the meta-circular evaluator

;; Bootstrap: load the meta-circular evaluator
;; (This is the "level 0 interpreter" running at the base)

;; === Level 0: Computation ===
;; Run fib through the meta-circular evaluator
(meta-eval '(defun fib (n)
              (if (< n 2) n
                (+ (fib (- n 1)) (fib (- n 2)))))
           base-env
           (lambda (v) v))

(meta-eval '(fib 8) base-env
           (lambda (result)
             (print "Level 0 result:" result)

             ;; === Level 1: Ground verification ===
             ;; (Same as before — probe the Cayley table via IO)
             (print "Verifying table...")
             ;; ... health check probes ...

             ;; === Level 2: Real reification ===
             ;; Now eval an expression that calls (reify)
             (meta-eval '(let ((state (reify)))
                           (print "Captured continuation")
                           (print "Environment size:"
                                  (length (cdr (assoc 'environment state))))
                           ;; Inject a binding
                           (let ((new-state
                                   (list (assoc 'continuation state)
                                         (cons 'environment
                                               (cons (cons 'ground-verified T)
                                                     (cdr (assoc 'environment state))))
                                         (assoc 'expression state))))
                             (reflect new-state 'done)))
                         base-env
                         (lambda (v)
                           ;; After reflect — ground-verified is now bound
                           (meta-eval 'ground-verified base-env
                             (lambda (gv)
                               (print "ground-verified =" gv)
                               (print "Tower complete.")))))))
```

## Integration with Existing Infrastructure

The meta-circular evaluator runs ON TOP of the existing `psi_lisp.py` evaluator. The base evaluator is the runtime. The meta-circular evaluator is a Ψ-Lisp program that the runtime executes. Programs run inside the meta-circular evaluator are doubly interpreted — but that's the whole point. The meta-level is a Ψ-Lisp program, which means it's inspectable, modifiable, and verifiable.

```
Layer 3: User program (fib 8)
         ↓ interpreted by
Layer 2: Meta-circular CPS evaluator (psi_metacircular.lisp)
         ↓ interpreted by
Layer 1: Base evaluator (psi_lisp.py / kamea-rs)
         ↓ executes via
Layer 0: Cayley table (256 bytes)
```

Level 1 (table verification) probes Layer 0.
Level 2 (reify/reflect) manipulates Layer 2's state.
The tower terminates at Layer 0, which is finite and verified.

## Implementation Plan

1. **Study the 3-Lisp repo.** Read the evaluator code. Understand how shift-up/shift-down work mechanically. Map the concepts to Ψ-Lisp's available primitives. Pay special attention to how continuations are represented and how the environment is threaded.

2. **Write `psi_metacircular.lisp`.** The CPS evaluator in pure Ψ-Lisp. Start with the core: `meta-eval`, `meta-apply`, `eval-args`, environment operations. Test it on simple expressions: `(meta-eval '(+ 1 2) base-env id)` should give 3.

3. **Add reify/reflect as cases in meta-eval.** Not builtins — just special forms that the meta-evaluator handles by manipulating the continuation.

4. **Write the tower demo.** Show all three levels: computation, table verification, evaluator reification with real environment modification via reflect.

5. **Test thoroughly.** The meta-circular evaluator should handle: arithmetic, conditionals, lambda, defun, let, recursive functions, list operations. It doesn't need to handle everything psi_lisp.py handles — just enough for the demo to be convincing.

## What This Achieves

- **Real reification.** The continuation is a Ψ∗ term — a lambda closure — not a Python stack frame. The program can inspect it because it's Lisp data.
- **Real reflection.** `(reflect)` jumps to a captured/modified continuation. The program genuinely alters its own future.
- **Grounded tower.** Unlike 3-Lisp, Level 1 verifies the Cayley table before the meta-evaluator is trusted. The tower has a proved foundation.
- **CPS evaluator as machine specification.** The meta-circular evaluator in CPS is a state machine. It could, in principle, be compiled down to Cayley table dispatch. This is the Scheme-79 insight applied to Ψ.
- **Meta-circular closure.** Ψ-Lisp interpreting Ψ-Lisp. The seven role-bearing atoms (from five axiom-forced categories) that implement the language are the same atoms the meta-circular evaluator is built from. The language interprets itself using itself.

## What NOT to Do

- Don't add reify/reflect as Python builtins in psi_lisp.py. They must emerge from the CPS structure of the meta-circular evaluator. That's the whole point.
- Don't try to implement the infinite tower. Two explicit levels (base + meta) with reify/reflect at the meta level is sufficient.
- Don't sacrifice correctness for the demo. If the meta-circular evaluator can only handle a subset of Ψ-Lisp, document what's supported. An honest partial implementation is better than a broken full one.
- Don't break existing files. The meta-circular evaluator is a new .lisp file. psi_lisp.py should need zero changes (or minimal ones, like ensuring closures are inspectable).

## Success Criteria

1. `(meta-eval '(+ 1 2) base-env id)` → 3
2. `(meta-eval '(fib 8) base-env id)` → 21 (with fib defined in base-env)
3. `(meta-eval '(reify) base-env id)` → a Lisp data structure containing the continuation and environment
4. Reify, modify environment, reflect, observe the modification take effect
5. Full tower demo runs and produces output showing all three levels with real reification
6. Someone reading the 3-Lisp repo can look at our meta-circular evaluator and recognize the same architecture — CPS evaluation with explicit continuations, reify as continuation capture, reflect as continuation installation

## Files

| File | Status |
|------|--------|
| `examples/psi_metacircular.lisp` | New: CPS meta-circular evaluator (~200-300 lines) |
| `examples/psi_reflective_tower.lisp` | Updated: use meta-circular evaluator for Level 2 |
| `psi_lisp.py` | Minimal or zero changes |
| `kamea-rs/` | No changes — Python first |
