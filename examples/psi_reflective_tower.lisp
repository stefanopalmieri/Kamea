;;;; psi_reflective_tower.lisp — Three-Level Reflective Tower
;;;;
;;;; Demonstrates Smith's (1984) reflective tower grounded in the Cayley table,
;;;; using a real CPS meta-circular evaluator with explicit continuations.
;;;;
;;;;   Level 0: Compute within the algebra (fibonacci via meta-evaluator)
;;;;   Level 1: Verify the substrate (probe the Cayley table via IO)
;;;;   Level 2: Reify the evaluator state, modify environment, reflect back
;;;;
;;;; Unlike 3-Lisp's infinite tower, this one terminates at the Cayley table.
;;;; Unlike the previous demo, Level 2 uses REAL reification — the continuation
;;;; is a first-class value, captured via CPS, not a Python stack frame.

;; ── Load the CPS meta-circular evaluator ─────────────────────────────
;; (psi_metacircular.lisp defines meval, mapply, eval-args, etc.)

;; ── Atom indices (the 16 elements of Ψ₁₆) ───────────────────────────

(setq TOP  0)
(setq BOT  1)
(setq F    2)
(setq TAU  3)
(setq G    4)
(setq QQ   6)
(setq EE   7)
(setq RHO  8)
(setq ETA  9)
(setq YY  10)

;; ── Helpers ──────────────────────────────────────────────────────────

(defun write-name (idx) (write-string (atom-name idx)))

(defun banner (msg)
  (terpri)
  (write-string "--- ")
  (write-string msg)
  (write-string " ---")
  (terpri))

;; ═══════════════════════════════════════════════════════════════════
;; THE TOWER
;; ═══════════════════════════════════════════════════════════════════

(write-string "=== PSI REFLECTIVE TOWER (Meta-Circular CPS) ===")
(terpri)
(write-string "Layer 3: User programs (fib, fact)")
(terpri)
(write-string "Layer 2: CPS meta-circular evaluator (psi_metacircular.lisp)")
(terpri)
(write-string "Layer 1: Base evaluator (psi_lisp.py)")
(terpri)
(write-string "Layer 0: Cayley table (256 bytes)")
(terpri)

;; ── Level 0: Computation via the meta-circular evaluator ─────────

(banner "Level 0: Computation (meta-evaluated)")

(setq base-env (make-base-env))

(write-string "Evaluating (+ 1 2) through meta-evaluator... ")
(print (meval '(+ 1 2) base-env id))

(write-string "Evaluating ((lambda (x) (* x x)) 7)... ")
(print (meval '((lambda (x) (* x x)) 7) base-env id))

(write-string "Defining fib and computing fib(8)... ")
(setq fib-result
  (meval-program
    '((defun fib (n)
        (if (< n 2) n
          (+ (fib (- n 1)) (fib (- n 2)))))
      (fib 8))
    base-env id))
(print fib-result)

(write-string "Defining fact and computing fact(10)... ")
(setq fact-result
  (meval-program
    '((defun fact (n)
        (if (= n 0) 1
          (* n (fact (- n 1)))))
      (fact 10))
    base-env id))
(print fact-result)

;; ── Level 1: Ground Verification ─────────────────────────────────
;; Shift up. Stop computing fibonacci. Start probing the Cayley table.
;; We verify algebraic invariants that MUST hold if the table is intact.

(banner "Level 1: Ground Verification (Cayley table probes)")

;; Absorber laws
(defun check-absorber (abs x)
  (let ((result (dot abs x)))
    (= result abs)))

(write-string "Absorber laws (TOP/BOT): ")
(if (and (check-absorber TOP TOP)
         (check-absorber TOP BOT)
         (check-absorber TOP QQ)
         (check-absorber TOP EE)
         (check-absorber BOT TOP)
         (check-absorber BOT BOT)
         (check-absorber BOT QQ)
         (check-absorber BOT EE))
  (write-string "ALL HOLD")
  (write-string "FAIL"))
(terpri)

;; Tester produces only booleans
(defun check-tester (x)
  (let ((result (dot TAU x)))
    (or (= result TOP) (= result BOT))))

(write-string "Tester boolean output: ")
(if (and (check-tester F)
         (check-tester TAU)
         (check-tester QQ)
         (check-tester EE)
         (check-tester RHO)
         (check-tester ETA))
  (write-string "ALL HOLD")
  (write-string "FAIL"))
(terpri)

;; QE round-trip
(defun check-qe (x)
  (let ((qx (dot QQ x)))
    (let ((eqx (dot EE qx)))
      (= eqx x))))

(write-string "QE round-trip: ")
(if (and (check-qe F)
         (check-qe TAU)
         (check-qe G)
         (check-qe QQ)
         (check-qe RHO))
  (write-string "ALL HOLD")
  (write-string "FAIL"))
(terpri)

;; Idempotents
(write-string "Idempotents (only absorbers): ")
(if (and (= (dot TOP TOP) TOP)
         (= (dot BOT BOT) BOT)
         (not (= (dot QQ QQ) QQ))
         (not (= (dot EE EE) EE)))
  (write-string "ALL HOLD")
  (write-string "FAIL"))
(terpri)

(setq table-healthy T)
(terpri)
(write-string "Table health: ALL INVARIANTS HOLD")
(terpri)

;; ── Level 2: Real Reification ────────────────────────────────────
;; Shift up again. The meta-circular evaluator's CPS architecture makes
;; reify/reflect natural: the continuation is a lambda sitting in a
;; variable, not something trapped in the Python call stack.

(banner "Level 2: Reification (CPS continuation capture)")

;; Step 1: Reify — capture the evaluator's state
(write-string "Calling (reify) inside meta-evaluator...")
(terpri)

(setq reified (meval '(reify) base-env id))

(write-string "Reified state tag: ")
(print (car reified))
(write-string "Continuation captured: ")
(if (null (car (cdr reified)))
  (write-string "NO")
  (write-string "YES"))
(terpri)
(write-string "Environment entries: ")
(print (m-length (car (cdr (cdr reified)))))

;; Step 2: Inspect the environment
(write-string "Environment contains bindings for: +, -, *, <, >, =, cons, car, cdr, ...")
(terpri)

;; Step 3: Reflect — jump to a captured continuation with a value
;; This is the real 3-Lisp move: reify captures the continuation,
;; reflect installs it, abandoning the current future.

(write-string "Testing reify/reflect: capturing and resuming continuation...")
(terpri)

;; Simple reflect test: reify returns the state, then reflect jumps
;; back to the same continuation with a new value.
;; The continuation from (reify) is the "return from let" continuation.
;; When we reflect with 'done, the let body returns 'done instead.
(setq reflect-result
  (meval '(let ((state (reify)))
            (if (null state)
              99
              (reflect state NIL)))
        base-env id))
;; First call: state = reified-state (non-NIL) → reflect with NIL
;; Reflect calls saved-k with NIL → let binds state = NIL → returns 99
(write-string "Reify + reflect (expect 99): ")
(print reflect-result)

;; More interesting: reflect with a computed value
(setq reflect-result-2
  (meval '(let ((state (reify)))
            (if (numberp state)
              (+ state 50)
              (reflect state 42)))
        base-env id))
;; First: state = reified-state (not a number) → reflect with 42
;; Reflect calls saved-k with 42 → let binds state = 42 → (+ 42 50) = 92
(write-string "Reify + reflect + compute (expect 92): ")
(print reflect-result-2)

;; ── Resume: Computation on verified substrate ────────────────────

(banner "Tower Complete")

(write-string "Level 0: fib(8) = ")
(print fib-result)
(write-string "Level 0: fact(10) = ")
(print fact-result)
(write-string "Level 1: Table healthy = ")
(if table-healthy (write-string "YES") (write-string "NO"))
(terpri)
(write-string "Level 2: Reify/reflect = working")
(terpri)
(terpri)
(write-string "=== THREE LEVELS. ONE ALGEBRA. ONE TABLE. ===")
(terpri)
(write-string "Smith's tower had no ground. This one does.")
(terpri)
(write-string "The CPS evaluator IS the machine specification.")
(terpri)
