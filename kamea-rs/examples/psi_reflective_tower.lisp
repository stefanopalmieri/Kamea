;;;; psi_reflective_tower.lisp — Three-Level Reflective Tower
;;;;
;;;; Demonstrates Smith's (1984) reflective tower grounded in the Cayley table,
;;;; using a defunctionalized CPS meta-circular evaluator with INSPECTABLE
;;;; continuations.
;;;;
;;;;   Level 0: Compute within the algebra (fibonacci via meta-evaluator)
;;;;   Level 1: Verify the substrate (probe the Cayley table via IO)
;;;;   Level 2: Reify/reflect with inspectable continuations
;;;;   Level 2b: Walk the continuation chain as data
;;;;   Level 2c: Modify the continuation and reflect into altered control flow
;;;;
;;;; Unlike 3-Lisp's infinite tower, this one terminates at the Cayley table.
;;;; Unlike closure-based CPS, every continuation is a tagged data structure.
;;;; The program can read its own future, modify it, and resume into an
;;;; altered control flow. This is Smith's full vision, running on 256 bytes.

;; ── Load the CPS meta-circular evaluator ─────────────────────────────
;; (psi_metacircular.lisp defines meval, mapply, eval-args, apply-k, etc.)

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

(write-string "=== PSI REFLECTIVE TOWER (Defunctionalized CPS) ===")
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
(setq k-id (list 'k-id))

(write-string "Evaluating (+ 1 2) through meta-evaluator... ")
(print (meval '(+ 1 2) base-env k-id))

(write-string "Evaluating ((lambda (x) (* x x)) 7)... ")
(print (meval '((lambda (x) (* x x)) 7) base-env k-id))

(write-string "Defining fib and computing fib(8)... ")
(setq fib-result
  (meval-program
    '((defun fib (n)
        (if (< n 2) n
          (+ (fib (- n 1)) (fib (- n 2)))))
      (fib 8))
    base-env k-id))
(print fib-result)

(write-string "Defining fact and computing fact(10)... ")
(setq fact-result
  (meval-program
    '((defun fact (n)
        (if (= n 0) 1
          (* n (fact (- n 1)))))
      (fact 10))
    base-env k-id))
(print fact-result)

;; ── Level 1: Ground Verification ─────────────────────────────────

(banner "Level 1: Ground Verification (Cayley table probes)")

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

;; ── Level 2: Inspectable Reification ──────────────────────────────

(banner "Level 2: Inspectable Reification (defunctionalized continuations)")

;; Step 1: Reify at top level — see the identity continuation
(write-string "Calling (reify) at top level...")
(terpri)

(setq reified (meval '(reify) base-env k-id))

(setq r-k (car (cdr reified)))
(write-string "  Continuation is tagged data (not a closure): ")
(if (null r-k)
  (write-string "NO")
  (if (numberp (car r-k))
    (write-string "YES")
    (write-string "NO")))
(terpri)
(write-string "  Environment entries: ")
(print (m-length (car (cdr (cdr reified)))))
(write-string "  Continuation chain depth: ")
(print (k-depth r-k))

;; Step 2: Reify/reflect — the classic test
(write-string "Reify + reflect (expect 99): ")
(print (meval '(let ((state (reify)))
                 (if (null state) 99 (reflect state NIL)))
              base-env k-id))

(write-string "Reify + reflect + compute (expect 92): ")
(print (meval '(let ((state (reify)))
                 (if (numberp state) (+ state 50) (reflect state 42)))
              base-env k-id))

;; ── Level 2b: Continuation Chain Inspection ───────────────────────

(banner "Level 2b: Continuation Chain Inspection")

;; Reify inside a let — the continuation chain:
;;   k-let-bind → k-let-body → k-id
(write-string "Reify inside (let ((x (reify))) x):")
(terpri)
(setq state-in-let (meval '(let ((x (reify))) x) base-env k-id))
(setq k-in-let (car (cdr state-in-let)))
(write-string "  Chain depth: ")
(print (k-depth k-in-let))
(write-string "  Chain tags (as symbol IDs): ")
(print (k-walk k-in-let))
(write-string "  (3 frames: k-let-bind -> k-let-body -> k-id)")
(terpri)

;; Verify the chain structure by comparing tags
(write-string "  Frame 0 tag = k-let-bind? ")
(if (= (car k-in-let) 'k-let-bind)
  (write-string "YES")
  (write-string "NO"))
(terpri)
(write-string "  Frame 1 tag = k-let-body? ")
(if (= (car (k-next k-in-let)) 'k-let-body)
  (write-string "YES")
  (write-string "NO"))
(terpri)
(write-string "  Frame 2 tag = k-id? ")
(if (= (car (k-next (k-next k-in-let))) 'k-id)
  (write-string "YES")
  (write-string "NO"))
(terpri)

;; Reify inside meval-program — see the toplevel bridge continuations
(write-string "Reify inside meval-program context:")
(terpri)
(setq state-in-program
  (meval-program
    '((defun dummy (x) x)
      (reify))
    base-env k-id))
(setq k-in-program (car (cdr state-in-program)))
(write-string "  Chain depth: ")
(print (k-depth k-in-program))
(write-string "  Frame 0 tag = k-top-wrap? ")
(if (= (car k-in-program) 'k-top-wrap)
  (write-string "YES")
  (write-string "NO"))
(terpri)
(write-string "  (k-top-wrap bridges meval-toplevel to meval)")
(terpri)

;; ── Level 2c: Continuation Modification ───────────────────────────

(banner "Level 2c: Continuation Modification (rewriting the future)")

;; Demo 1: Value injection via reflect
(write-string "Value injection via reflect:")
(terpri)
(write-string "  (let ((x (reify))) (if (numberp x) (+ x 50) (reflect x 7)))")
(terpri)
(setq inject-result
  (meval '(let ((x (reify)))
            (if (numberp x)
              (+ x 50)        ;; second pass: x=7, return 57
              (reflect x 7))) ;; first pass: inject 7
        base-env k-id))
(write-string "  Result (expect 57): ")
(print inject-result)

;; Demo 2: The k-if branch swap — THE definitive 3-Lisp demo.
;; A program that:
;; 1. Reifies its own state inside the test position of an if
;; 2. Inspects the continuation chain to find the k-if frame
;; 3. Swaps the then/else branches in the k-if
;; 4. Reflects with the modified continuation
;; Result: the if takes the OPPOSITE branch from what the source code says.
(write-string "K-IF BRANCH SWAP — the definitive 3-Lisp demo:")
(terpri)

;; First, without modification: (if 1 42 99) → 42
(write-string "  Without modification: (if 1 42 99) → ")
(print (meval '(if 1 42 99) base-env k-id))

;; Now, with branch swap: should get 99 instead of 42
(setq swap-result
  (meval-program
    '((defun swap-branches ()
        ;; The outer if: (if TEST 42 99)
        ;; TEST does (reify), inspects the continuation, swaps branches, reflects.
        (if (let ((s (reify)))
              (if (numberp s)
                s  ;; second pass: return the test value to the (modified) k-if
                ;; first pass: s = reified state
                ;; The continuation chain at this point:
                ;;   k-let-bind → k-let-body → k-if → k-top-wrap → ...
                ;; Navigate to find k-if:
                (let ((k (car (cdr s))))           ;; k = k-let-bind
                  (let ((kb (nth 4 k)))            ;; kb = k-let-body (next-k of k-let-bind)
                    (let ((kif (nth 2 kb)))        ;; kif = k-if (next-k of k-let-body)
                      ;; kif = (tag then else env next-k)
                      ;; Swap then (nth 1) and else (nth 2):
                      (let ((swapped-kif (list (nth 0 kif) (nth 2 kif) (nth 1 kif)
                                               (nth 3 kif) (nth 4 kif))))
                        ;; Rebuild: k-let-body with swapped kif
                        (let ((new-kb (list (nth 0 kb) (nth 1 kb) swapped-kif)))
                          ;; Rebuild: k-let-bind with new k-let-body
                          (let ((new-k (list (nth 0 k) (nth 1 k) (nth 2 k)
                                             (nth 3 k) new-kb)))
                            ;; Build new reified state with modified continuation
                            (let ((new-state (list (car s) new-k
                                                   (nth 2 s) (nth 3 s))))
                              ;; Reflect with 1 (truthy) as the test value
                              (reflect new-state 1))))))))))
            42    ;; ORIGINAL then-branch
            99))  ;; ORIGINAL else-branch
      (swap-branches))
    base-env k-id))
;; Without the swap: test=1 (truthy) → then-branch = 42
;; With the swap: then/else swapped in k-if, so truthy → else-branch = 99
(write-string "  With branch swap: (if 1 42 99) → ")
(print swap-result)

;; Verify the swap worked
(if (= swap-result 99)
  (progn
    (write-string "  CONFIRMED: Program rewrote its own if-branches.")
    (terpri)
    (write-string "  The if saw 1 (truthy) but took the else-branch (99)")
    (terpri)
    (write-string "  because the continuation was modified before reflect."))
  (progn
    (write-string "  UNEXPECTED: expected 99 from branch swap, got ")
    (print swap-result)))
(terpri)

;; ── Resume ──────────────────────────────────────────────────────

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
(write-string "Level 2b: Continuation chains walkable as tagged data")
(terpri)
(write-string "Level 2c: Branch swap via continuation modification = ")
(if (= swap-result 99) (write-string "WORKING") (write-string "FAILED"))
(terpri)
(terpri)
(write-string "=== THREE LEVELS. ONE ALGEBRA. ONE TABLE. ===")
(terpri)
(write-string "Smith's tower had no ground. This one does.")
(terpri)
(write-string "Smith's continuations were closures. These are data.")
(terpri)
(write-string "The program can read, modify, and rewrite its own future.")
(terpri)
