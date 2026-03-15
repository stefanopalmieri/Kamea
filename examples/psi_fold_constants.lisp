;;; psi_fold_constants.lisp — Compile-time Cayley table constant folding
;;;
;;; Walks an expression tree of (dot A B) nodes and replaces any node
;;; where both operands are known atom indices (0-15) with the result
;;; of the Cayley table lookup. Demonstrates the algebra as a partial
;;; evaluator for its own operation.
;;;
;;; Two modes:
;;;   fold-step  — one pass: folds innermost foldable nodes, no cascade
;;;   fold-all   — full bottom-up: folds everything in one recursive pass

;; ── Atom indices ─────────────────────────────────────────────────────

(setq INC 13)
(setq DEC 15)
(setq s0  12)

;; ── Expression tree tag ──────────────────────────────────────────────
;; Expression trees are data (quoted), not code. Dot-application nodes
;; use the symbol 'dot as a tag: (dot A B) where A, B are sub-expressions
;; or atom indices 0-15.

(setq DOT-TAG 'dot)

;; ── Predicates ───────────────────────────────────────────────────────

(defun atom-idx? (x)
  "True if x is a resolved atom index (0-15)."
  (if (numberp x) (< x 16) NIL))

;; ── Constructors ─────────────────────────────────────────────────────

(defun mk-dot (a b) (list DOT-TAG a b))

;; ── Display ──────────────────────────────────────────────────────────

(defun counter-name (idx)
  "Map atom index to readable name. Prefer role names for Q, E, tau."
  (cond
    ((= idx  6) "Q")   ((= idx  7) "E")   ((= idx  3) "tau")
    ((= idx 13) "INC") ((= idx 15) "DEC")
    ((= idx  0) "TOP") ((= idx  1) "BOT")
    ((= idx 12) "s0")  ((= idx 14) "s1")
    ((= idx 11) "s3")  ((= idx 10) "s4")
    ((= idx  8) "s6")
    (T (atom-name idx))))

(defun show-expr (expr)
  "Print an expression tree with counter-state names."
  (if (null expr) (write-string "NIL")
    (if (numberp expr)
      (if (atom-idx? expr)
        (write-string (counter-name expr))
        (display expr))
      (let ((head (car expr)))
        (cond
          ((= head DOT-TAG)
            (progn
              (write-string "(dot ")
              (show-expr (car (cdr expr)))
              (write-string " ")
              (show-expr (car (cdr (cdr expr))))
              (write-string ")")))
          ((= head IF-TAG)
            (progn
              (write-string "(if ")
              (show-expr (car (cdr expr)))
              (write-string " ")
              (show-expr (car (cdr (cdr expr))))
              (write-string " ")
              (show-expr (car (cdr (cdr (cdr expr)))))
              (write-string ")")))
          (T (progn
              (write-string "(? ")
              (display expr)
              (write-string ")"))))))))

;; ── fold-step: one pass ──────────────────────────────────────────────
;; Recurses into compound sub-expressions to find foldable leaves.
;; When (dot A B) has both A and B already resolved to atom indices,
;; replaces with the Cayley table result. Does NOT re-examine the
;; result — cascading requires another pass.

(defun fold-step (expr)
  (if (leaf? expr) expr
    (if (null expr) expr
      (let ((head (car expr)))
        (cond
          ((= head DOT-TAG)
            (let ((a (car (cdr expr)))
                  (b (car (cdr (cdr expr)))))
              (if (atom-idx? a)
                (if (atom-idx? b)
                  (dot a b)
                  (list DOT-TAG a (fold-step b)))
                (if (atom-idx? b)
                  (list DOT-TAG (fold-step a) b)
                  (list DOT-TAG (fold-step a) (fold-step b))))))
          ((= head IF-TAG)
            (let ((test (car (cdr expr)))
                  (then-b (car (cdr (cdr expr))))
                  (else-b (car (cdr (cdr (cdr expr))))))
              (if (atom-idx? test)
                (if (= test 1) else-b then-b)
                (list IF-TAG (fold-step test)
                      (fold-step then-b)
                      (fold-step else-b)))))
          (T expr))))))

;; ── fold-all: full bottom-up reduction ───────────────────────────────
;; Recursively folds sub-expressions first, then folds the parent if
;; both children resolved. Reduces the entire tree in one pass.
;;
;; Handles:
;;   (dot A B)     — Cayley table lookup when both A, B are known atoms
;;   (dot E (dot Q x)) → x   — QE cancellation (Lean-proved inverse law)
;;   (dot Q (dot E x)) → x   — EQ cancellation (Lean-proved inverse law)
;;   (if T X Y)    — dead branch elimination when test is a known atom
;;                   (BOT = falsy → Y, any other atom = truthy → X)

(setq IF-TAG 'if)
(setq Q-IDX 6)   ;; Q = element 6
(setq E-IDX 7)   ;; E = element 7

(defun dot-node? (expr)
  "True if expr is a (dot ...) node."
  (if (null expr) NIL
    (if (numberp expr) NIL
      (= (car expr) DOT-TAG))))

(defun dot-arg1 (expr) (car (cdr expr)))
(defun dot-arg2 (expr) (car (cdr (cdr expr))))

(defun fold-all (expr)
  (if (leaf? expr) expr
    (if (null expr) expr
      (let ((head (car expr)))
        (cond
          ;; (dot A B) — constant fold, with QE cancellation
          ((= head DOT-TAG)
            (let ((a-expr (car (cdr expr)))
                  (b-expr (car (cdr (cdr expr)))))
              ;; Fold the left operand first
              (let ((a (fold-all a-expr)))
                ;; QE cancellation checked on RAW b (before folding would
                ;; resolve the inner dot via the Cayley table). This is a
                ;; term algebra law: E·(Q·x) = x, Q·(E·x) = x.
                (cond
                  ;; E·(Q·x) → x
                  ((if (= a E-IDX) (if (dot-node? b-expr) (= (dot-arg1 b-expr) Q-IDX) NIL) NIL)
                    (fold-all (dot-arg2 b-expr)))
                  ;; Q·(E·x) → x
                  ((if (= a Q-IDX) (if (dot-node? b-expr) (= (dot-arg1 b-expr) E-IDX) NIL) NIL)
                    (fold-all (dot-arg2 b-expr)))
                  ;; No QE pattern — fold b normally, then try table lookup
                  (T (let ((b (fold-all b-expr)))
                       (cond
                         ((if (atom-idx? a) (atom-idx? b) NIL)
                           (dot a b))
                         ;; Post-fold QE check (b might have become a dot-node)
                         ((if (= a E-IDX) (if (dot-node? b) (= (dot-arg1 b) Q-IDX) NIL) NIL)
                           (dot-arg2 b))
                         ((if (= a Q-IDX) (if (dot-node? b) (= (dot-arg1 b) E-IDX) NIL) NIL)
                           (dot-arg2 b))
                         (T (list DOT-TAG a b)))))))))

          ;; (if test then else) — dead branch elimination
          ((= head IF-TAG)
            (let ((test (fold-all (car (cdr expr))))
                  (then-b (car (cdr (cdr expr))))
                  (else-b (car (cdr (cdr (cdr expr))))))
              (if (atom-idx? test)
                ;; test resolved: BOT is falsy, everything else truthy
                (if (= test 1)
                  (fold-all else-b)
                  (fold-all then-b))
                ;; test not resolved: fold branches but keep the if
                (list IF-TAG test
                      (fold-all then-b)
                      (fold-all else-b)))))

          ;; anything else: return as-is
          (T expr))))))

;; ── Tracing ──────────────────────────────────────────────────────────

(defun leaf? (expr)
  "True if expr is fully reduced (atom index or plain number)."
  (if (null expr) T
    (if (numberp expr) T
      NIL)))

(defun fold-show (expr n)
  "Fold step-by-step, printing each intermediate form."
  (write-string "  step ")
  (display n)
  (write-string ":  ")
  (show-expr expr)
  (terpri)
  (if (leaf? expr) expr
    (fold-show (fold-step expr) (+ n 1))))

;; ═════════════════════════════════════════════════════════════════════
;; TESTS
;; ═════════════════════════════════════════════════════════════════════

(write-string "=== Constant Folding: Cayley Table Partial Evaluation ===")
(terpri)

;; ── Test 1: INC^3 · s0 ──────────────────────────────────────────────
;; Counter cycle: s0 →INC→ s1 →INC→ s2 →INC→ s3

(terpri)
(write-string "--- INC^3 applied to s0 (expect s3) ---")
(terpri)
(setq expr1 (mk-dot INC (mk-dot INC (mk-dot INC s0))))
(setq _ (fold-show expr1 0))

;; ── Test 2: INC^8 · s0 (full cycle back to s0) ──────────────────────

(terpri)
(write-string "--- INC^8 applied to s0 (full cycle, expect s0) ---")
(terpri)
(setq expr2
  (mk-dot INC (mk-dot INC (mk-dot INC (mk-dot INC
  (mk-dot INC (mk-dot INC (mk-dot INC (mk-dot INC s0)))))))))
(setq _ (fold-show expr2 0))

;; ── Test 3: DEC reverses INC ─────────────────────────────────────────
;; DEC · INC · INC · s0 = DEC · s2 = s1

(terpri)
(write-string "--- DEC(INC(INC(s0))) (expect s1) ---")
(terpri)
(setq expr3 (mk-dot DEC (mk-dot INC (mk-dot INC s0))))
(setq _ (fold-show expr3 0))

;; ── Test 4: INC · DEC · INC · s0 ────────────────────────────────────
;; INC(s0)=s1, DEC(s1)=s0, INC(s0)=s1

(terpri)
(write-string "--- INC(DEC(INC(s0))) (expect s1) ---")
(terpri)
(setq expr4 (mk-dot INC (mk-dot DEC (mk-dot INC s0))))
(setq _ (fold-show expr4 0))

;; ── Test 5: fold-all does it in one pass ─────────────────────────────

(terpri)
(write-string "--- fold-all: full reduction in one pass ---")
(terpri)
(write-string "  input:   ")
(show-expr expr1)
(terpri)
(write-string "  result:  ")
(show-expr (fold-all expr1))
(terpri)
(terpri)
(write-string "  input:   ")
(show-expr expr2)
(terpri)
(write-string "  result:  ")
(show-expr (fold-all expr2))
(terpri)

;; ── Test 6: Absorber short-circuits ──────────────────────────────────
;; TOP · anything = TOP

(terpri)
(write-string "--- TOP absorbs: dot(TOP, INC(INC(s0))) ---")
(terpri)
(setq expr5 (mk-dot 0 (mk-dot INC (mk-dot INC s0))))
(write-string "  input:   ")
(show-expr expr5)
(terpri)
(write-string "  result:  ")
(show-expr (fold-all expr5))
(terpri)

;; ═════════════════════════════════════════════════════════════════════
;; DEAD BRANCH ELIMINATION
;; ═════════════════════════════════════════════════════════════════════

(defun mk-if (test then else-b) (list IF-TAG test then else-b))

(terpri)
(write-string "=== Dead Branch Elimination ===")
(terpri)

;; ── Test 7: Known truthy test ────────────────────────────────────────
;; TOP (=0) is truthy (not BOT), select then-branch

(terpri)
(write-string "--- (if TOP 42 99) → 42 ---")
(terpri)
(setq expr6 (mk-if 0 42 99))
(write-string "  input:   ") (show-expr expr6) (terpri)
(write-string "  result:  ") (show-expr (fold-all expr6)) (terpri)

;; ── Test 8: Known falsy test ─────────────────────────────────────────
;; BOT (=1) is falsy, select else-branch

(terpri)
(write-string "--- (if BOT 42 99) → 99 ---")
(terpri)
(setq expr7 (mk-if 1 42 99))
(write-string "  input:   ") (show-expr expr7) (terpri)
(write-string "  result:  ") (show-expr (fold-all expr7)) (terpri)

;; ── Test 9: Cascading — dot fold feeds branch elimination ────────────
;; tau·s0 = TOP (tester accepts s0), so the if resolves to then-branch.
;; Two Cayley lookups and a branch, all eliminated at compile time.

(terpri)
(write-string "--- (if (dot tau s0) 42 99) → 42 ---")
(terpri)
(setq TAU 3)
(setq expr8 (mk-if (mk-dot TAU s0) 42 99))
(write-string "  input:   ") (show-expr expr8) (terpri)
(write-string "  result:  ") (show-expr (fold-all expr8)) (terpri)

;; ── Test 10: tau rejects non-zero counter states ─────────────────────
;; tau·s1 = BOT (tester rejects s1), so the if resolves to else-branch.

(terpri)
(write-string "--- (if (dot tau s1) 42 99) → 99 ---")
(terpri)
(setq s1 14)
(setq expr9 (mk-if (mk-dot TAU s1) 42 99))
(write-string "  input:   ") (show-expr expr9) (terpri)
(write-string "  result:  ") (show-expr (fold-all expr9)) (terpri)

;; ── Test 11: Full cascade — INC, then test, then branch ──────────────
;; (if (dot tau (dot INC s0)) 42 99)
;; → (if (dot tau s1) 42 99)     fold INC·s0 = s1
;; → (if BOT 42 99)              fold tau·s1 = BOT
;; → 99                          branch elimination

(terpri)
(write-string "--- (if (dot tau (dot INC s0)) 42 99) → 99 ---")
(terpri)
(setq expr10 (mk-if (mk-dot TAU (mk-dot INC s0)) 42 99))
(write-string "  input:   ") (show-expr expr10) (terpri)
(write-string "  result:  ") (show-expr (fold-all expr10)) (terpri)
(write-string "  (INC·s0=s1, tau·s1=BOT, BOT is falsy → else-branch)")
(terpri)

;; ── Test 12: Step-by-step cascade ────────────────────────────────────

(terpri)
(write-string "--- Step-by-step: (if (dot tau (dot INC s0)) 42 99) ---")
(terpri)
(setq _ (fold-show expr10 0))

;; ═════════════════════════════════════════════════════════════════════
;; QE CANCELLATION
;; ═════════════════════════════════════════════════════════════════════

(terpri)
(write-string "=== QE Cancellation (Lean-proved inverse laws) ===")
(terpri)

(setq QQ 6)  ;; Q = element 6
(setq EE 7)  ;; E = element 7

;; ── Test 13: E·(Q·x) → x ────────────────────────────────────────────

(terpri)
(write-string "--- (dot E (dot Q s0)) → s0 ---")
(terpri)
(setq qe1 (mk-dot EE (mk-dot QQ s0)))
(write-string "  input:   ") (show-expr qe1) (terpri)
(write-string "  result:  ") (show-expr (fold-all qe1)) (terpri)

;; ── Test 14: Q·(E·x) → x ────────────────────────────────────────────

(terpri)
(write-string "--- (dot Q (dot E s0)) → s0 ---")
(terpri)
(setq qe2 (mk-dot QQ (mk-dot EE s0)))
(write-string "  input:   ") (show-expr qe2) (terpri)
(write-string "  result:  ") (show-expr (fold-all qe2)) (terpri)

;; ── Test 15: QE inside larger expression ─────────────────────────────
;; (dot INC (dot E (dot Q s0))) → (dot INC s0) → s1

(terpri)
(write-string "--- (dot INC (dot E (dot Q s0))) → s1 ---")
(terpri)
(setq qe3 (mk-dot INC (mk-dot EE (mk-dot QQ s0))))
(write-string "  input:   ") (show-expr qe3) (terpri)
(write-string "  result:  ") (show-expr (fold-all qe3)) (terpri)

;; ── Test 16: Nested QE cancellation ──────────────────────────────────
;; (dot E (dot Q (dot E (dot Q s0)))) → s0

(terpri)
(write-string "--- (dot E (dot Q (dot E (dot Q s0)))) → s0 ---")
(terpri)
(setq qe4 (mk-dot EE (mk-dot QQ (mk-dot EE (mk-dot QQ s0)))))
(write-string "  input:   ") (show-expr qe4) (terpri)
(write-string "  result:  ") (show-expr (fold-all qe4)) (terpri)

;; ── Test 17: QE with compound argument ───────────────────────────────
;; (dot E (dot Q (dot INC s0)))
;; QE cancellation fires on raw structure: E·(Q·x) → x where x = (dot INC s0).
;; Then INC·s0 folds to s1 via table.
;; Result: s1.

(terpri)
(write-string "--- (dot E (dot Q (dot INC s0))) → s1 ---")
(terpri)
(write-string "  QE cancels E·(Q·x) → x, then INC·s0 → s1 via table")
(terpri)
(setq qe5 (mk-dot EE (mk-dot QQ (mk-dot INC s0))))
(write-string "  input:   ") (show-expr qe5) (terpri)
(write-string "  result:  ") (show-expr (fold-all qe5)) (terpri)
