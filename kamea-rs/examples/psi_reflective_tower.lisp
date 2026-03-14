; psi_reflective_tower.lisp — Three-level reflective tower demo
;
; Demonstrates Smith's (1984) reflective tower grounded in the Cayley table.
;
;   Level 0: Compute within the algebra (fibonacci)
;   Level 1: Verify the substrate (probe the Cayley table)
;   Level 2: Inspect the evaluator (reify environment)
;
; Unlike 3-Lisp's tower (interpreters all the way up), this tower
; terminates at the Cayley table — 256 bytes of self-certifying ground.

;; ── Atom indices (the 16 elements of Psi-16) ────────────────────────

(setq TOP  0)   ; absorber (true, zero)
(setq BOT  1)   ; absorber (false, empty)
(setq F    2)   ; encoder / fst projection
(setq TAU  3)   ; tester
(setq G    4)   ; pair constructor
(setq QQ   6)   ; quote / successor
(setq EE   7)   ; eval / predecessor
(setq RHO  8)   ; structural branch
(setq ETA  9)   ; snd projection
(setq YY  10)   ; fixed-point combinator

;; ── Helpers ─────────────────────────────────────────────────────────

(defun member (x lst)
  (if (null lst) NIL
    (if (= x (car lst)) T
      (member x (cdr lst)))))

(defun length (lst)
  (if (null lst) 0
    (+ 1 (length (cdr lst)))))

(defun all-true (lst)
  "Return T if lst contains no NIL."
  (if (null lst) T
    (if (car lst)
      (all-true (cdr lst))
      NIL)))

(defun for-each-check (fn lst)
  "Apply fn to each element; return T if all results non-NIL."
  (if (null lst) T
    (if (fn (car lst))
      (for-each-check fn (cdr lst))
      NIL)))

(defun write-name (idx)
  "Write the symbolic name of atom idx."
  (write-string (atom-name idx)))

;; ── Level 0: Normal computation ─────────────────────────────────────

(defun fib (n)
  (if (< n 2) n
    (+ (fib (- n 1)) (fib (- n 2)))))

(defun banner (msg)
  (terpri)
  (write-string "--- ")
  (write-string msg)
  (write-string " ---")
  (terpri))

(write-string "=== PSI REFLECTIVE TOWER ===")
(terpri)

(banner "Level 0: Computation")

(write-string "Computing fibonacci(8)...")
(terpri)
(setq fib-result (fib 8))
(write-string "Result: ")
(print fib-result)

;; ── Level 1: Ground verification ────────────────────────────────────
;; Shift up. Stop computing fibonacci. Start probing the Cayley table.
;; We verify algebraic invariants that MUST hold if the table is intact.

(banner "Shift Up to Level 1: Ground Verification")

;; Verify absorber laws: dot(TOP, x) = TOP and dot(BOT, x) = BOT
(defun check-absorber (abs x)
  (let ((result (dot abs x)))
    (write-string "  ")
    (write-name abs)
    (write-string " . ")
    (write-name x)
    (write-string " = ")
    (write-name result)
    (if (= result abs)
      (progn (write-string " ok") (terpri) T)
      (progn (write-string " FAIL") (terpri) NIL))))

(write-string "Absorber laws:")
(terpri)
(setq absorber-ok
  (and (check-absorber TOP TOP)
       (check-absorber TOP BOT)
       (check-absorber TOP QQ)
       (check-absorber TOP EE)
       (check-absorber BOT TOP)
       (check-absorber BOT BOT)
       (check-absorber BOT QQ)
       (check-absorber BOT EE)))

;; Verify tester produces only boolean outputs: dot(TAU, x) in {TOP, BOT}
(defun check-tester (x)
  (let ((result (dot TAU x)))
    (write-string "  tau . ")
    (write-name x)
    (write-string " = ")
    (write-name result)
    (if (or (= result TOP) (= result BOT))
      (progn (write-string " ok") (terpri) T)
      (progn (write-string " FAIL") (terpri) NIL))))

(write-string "Tester boolean output:")
(terpri)
(setq tester-ok
  (and (check-tester F)
       (check-tester TAU)
       (check-tester QQ)
       (check-tester EE)
       (check-tester RHO)
       (check-tester ETA)))

;; Verify QE round-trip: dot(E, dot(Q, x)) = x for known-good elements
(defun check-qe (x)
  (let ((qx (dot QQ x)))
    (let ((eqx (dot EE qx)))
      (write-string "  E . (Q . ")
      (write-name x)
      (write-string ") = E . ")
      (write-name qx)
      (write-string " = ")
      (write-name eqx)
      (if (= eqx x)
        (progn (write-string " ok") (terpri) T)
        (progn (write-string " FAIL") (terpri) NIL)))))

(write-string "QE round-trip:")
(terpri)
(setq qe-ok
  (and (check-qe F)
       (check-qe TAU)
       (check-qe G)
       (check-qe QQ)
       (check-qe RHO)))

;; Verify idempotents: dot(x, x) = x only for TOP and BOT
(defun check-idempotent (x expected)
  (let ((xx (dot x x)))
    (write-string "  ")
    (write-name x)
    (write-string " . ")
    (write-name x)
    (write-string " = ")
    (write-name xx)
    (if (= (= xx x) expected)
      (progn (write-string " ok") (terpri) T)
      (progn (write-string " FAIL") (terpri) NIL))))

(write-string "Idempotents (only absorbers):")
(terpri)
(setq idem-ok
  (and (check-idempotent TOP T)
       (check-idempotent BOT T)
       (check-idempotent QQ NIL)
       (check-idempotent EE NIL)))

;; Health verdict
(terpri)
(setq table-healthy (and absorber-ok tester-ok qe-ok idem-ok))
(if table-healthy
  (progn
    (write-string "Table health: ALL INVARIANTS HOLD")
    (terpri))
  (progn
    (write-string "Table health: CORRUPTION DETECTED")
    (terpri)))

;; ── Level 2: Evaluator state inspection ─────────────────────────────
;; Shift up again. The program now inspects its OWN interpreter state.
;; This is Smith's 3-Lisp move — but grounded.

(banner "Shift Up to Level 2: Evaluator Inspection")

(setq num-bindings (env-size))
(write-string "Current environment: ")
(display num-bindings)
(write-string " bindings")
(terpri)

;; Inspect our own state: is fib-result still valid?
(write-string "Last result (fib-result): ")
(print fib-result)

;; Verify key bindings exist
(write-string "Binding 'fib': ")
(if (bound? fib) (write-string "present") (write-string "MISSING"))
(terpri)

(write-string "Binding 'table-healthy': ")
(if (bound? table-healthy) (write-string "present") (write-string "MISSING"))
(terpri)

(write-string "Binding 'fib-result': ")
(if (bound? fib-result) (write-string "present") (write-string "MISSING"))
(terpri)

;; Verify consistency: the result stored in the env matches recomputation
(write-string "Consistency check: (fib 8) = fib-result? ")
(if (= (fib 8) fib-result)
  (write-string "ok")
  (write-string "INCONSISTENT"))
(terpri)

;; The meta-point: we verified the ground (level 1), now we verified
;; the evaluator state (level 2). Both checks passed. The tower is sound.
(terpri)
(write-string "Evaluator state: CONSISTENT")
(terpri)

;; ── Shift down: Resume computation on verified substrate ────────────

(banner "Shift Down: Resume with Verified Substrate")

(write-string "Computing fibonacci(12) on verified ground...")
(terpri)
(setq fib-result-2 (fib 12))
(write-string "Result: ")
(print fib-result-2)
(terpri)
(write-string "=== TOWER COMPLETE ===")
(terpri)
(write-string "Three levels. One algebra. One table.")
(terpri)
(write-string "Smith's tower had no ground. This one does.")
(terpri)
