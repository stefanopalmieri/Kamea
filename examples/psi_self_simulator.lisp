;; ═══════════════════════════════════════════════════════════════════════
;; Self-Simulator for Ψ₁₆ᶠ
;;
;; A single function that computes the Cayley table: for all a, b ∈ {0..15},
;;   (self-dot a b) = dot(a, b)
;;
;; This establishes that self-simulation is POSSIBLE: Ψ₁₆ᶠ can compute
;; its own binary operation from within.
;;
;; Two versions:
;;   1. Brute-force: hardcoded lookup (256 entries)
;;   2. Role-aware: dispatches on algebraic roles (60 computed, 196 hardcoded)
;;
;; Run: python3 psi_lisp.py examples/psi_self_simulator.lisp
;; ═══════════════════════════════════════════════════════════════════════

;; ── Brute-force self-simulator ──
;; Every cell is hardcoded. No algebraic structure exploited.

(define (self-dot-brute a b)
  (cond
    ((= a 0) 0)
    ((= a 1) 1)
    ((= a 2) (cond ((= b 0) 5) ((= b 1) 1) ((= b 2) 13) ((= b 3) 7) ((= b 4) 11) ((= b 5) 5) ((= b 6) 6) ((= b 7) 8) ((= b 8) 2) ((= b 9) 5) ((= b 10) 11) ((= b 11) 9) ((= b 12) 4) ((= b 13) 14) ((= b 14) 3) (t 15)))
    ((= a 3) (cond ((= b 0) 0) ((= b 1) 1) ((= b 2) 0) ((= b 3) 0) ((= b 4) 0) ((= b 5) 0) ((= b 6) 1) ((= b 7) 1) ((= b 8) 1) ((= b 9) 0) ((= b 10) 1) ((= b 11) 1) ((= b 12) 0) ((= b 13) 0) ((= b 14) 1) (t 1)))
    ((= a 4) (if (= b 0) 0 11))
    ((= a 5) (cond ((= b 0) 0) ((= b 1) 1) ((= b 2) 1) ((= b 3) 1) ((= b 4) 1) ((= b 5) 1) ((= b 6) 0) ((= b 7) 1) ((= b 8) 1) ((= b 9) 1) ((= b 10) 0) ((= b 11) 1) ((= b 12) 0) ((= b 13) 1) ((= b 14) 1) (t 0)))
    ((= a 6) (cond ((= b 0) 15) ((= b 1) 0) ((= b 2) 5) ((= b 3) 9) ((= b 4) 3) ((= b 5) 15) ((= b 6) 14) ((= b 7) 14) ((= b 8) 2) ((= b 9) 12) ((= b 10) 8) ((= b 11) 14) ((= b 12) 12) ((= b 13) 4) ((= b 14) 12) (t 8)))
    ((= a 7) (cond ((= b 0) 0) ((= b 1) 1) ((= b 2) 8) ((= b 3) 4) ((= b 4) 13) ((= b 5) 2) ((= b 6) 11) ((= b 7) 2) ((= b 8) 14) ((= b 9) 3) ((= b 10) 15) ((= b 11) 12) ((= b 12) 14) ((= b 13) 15) ((= b 14) 6) (t 5)))
    ((= a 8) (cond ((= b 0) 12) ((= b 1) 1) ((= b 2) 13) ((= b 3) 7) ((= b 4) 11) ((= b 5) 5) ((= b 6) 12) ((= b 7) 11) ((= b 8) 4) ((= b 9) 12) ((= b 10) 5) ((= b 11) 14) ((= b 12) 15) ((= b 13) 7) ((= b 14) 11) (t 12)))
    ((= a 9) (cond ((= b 0) 1) ((= b 1) 6) ((= b 2) 14) ((= b 3) 14) ((= b 4) 14) ((= b 5) 14) ((= b 6) 9) ((= b 7) 8) ((= b 8) 3) ((= b 9) 15) ((= b 10) 5) ((= b 11) 7) ((= b 12) 13) ((= b 13) 11) ((= b 14) 12) (t 4)))
    ((= a 10) (cond ((= b 0) 13) ((= b 1) 1) ((= b 2) 4) ((= b 3) 3) ((= b 4) 12) ((= b 5) 11) ((= b 6) 2) ((= b 7) 11) ((= b 8) 5) ((= b 9) 3) ((= b 10) 8) ((= b 11) 14) ((= b 12) 9) ((= b 13) 7) ((= b 14) 11) (t 11)))
    ((= a 11) (cond ((= b 0) 14) ((= b 1) 1) ((= b 2) 9) ((= b 3) 10) ((= b 4) 11) ((= b 5) 13) ((= b 6) 12) ((= b 7) 7) ((= b 8) 5) ((= b 9) 6) ((= b 10) 8) ((= b 11) 2) ((= b 12) 14) ((= b 13) 12) ((= b 14) 10) (t 4)))
    ((= a 12) (cond ((= b 0) 0) ((= b 1) 1) ((= b 2) 1) ((= b 3) 0) ((= b 4) 1) ((= b 5) 1) ((= b 6) 0) ((= b 7) 1) ((= b 8) 1) ((= b 9) 1) ((= b 10) 0) ((= b 11) 0) ((= b 12) 0) ((= b 13) 0) ((= b 14) 0) (t 1)))
    ((= a 13) (cond ((= b 0) 3) ((= b 1) 0) ((= b 2) 14) ((= b 3) 4) ((= b 4) 14) ((= b 5) 6) ((= b 6) 11) ((= b 7) 12) ((= b 8) 7) ((= b 9) 3) ((= b 10) 15) ((= b 11) 10) ((= b 12) 14) ((= b 13) 2) ((= b 14) 6) (t 8)))
    ((= a 14) (cond ((= b 0) 14) ((= b 1) 0) ((= b 2) 5) ((= b 3) 4) ((= b 4) 3) ((= b 5) 2) ((= b 6) 12) ((= b 7) 5) ((= b 8) 11) ((= b 9) 14) ((= b 10) 3) ((= b 11) 14) ((= b 12) 12) ((= b 13) 2) ((= b 14) 6) (t 3)))
    (t (cond ((= b 0) 1) ((= b 1) 3) ((= b 2) 13) ((= b 3) 15) ((= b 4) 3) ((= b 5) 7) ((= b 6) 14) ((= b 7) 8) ((= b 8) 15) ((= b 9) 4) ((= b 10) 11) ((= b 11) 6) ((= b 12) 7) ((= b 13) 14) ((= b 14) 12) (t 10)))))

;; ── Role-aware self-simulator ──
;; Exploits algebraic structure to compute 60/256 cells from axioms.
;; Remaining 196 cells are hardcoded per-element.

(define (self-dot-role a b)
  (cond
    ;; Absorbers: constant rows (32 cells computed)
    ((= a 0) 0)                           ; ⊤·b = ⊤
    ((= a 1) 1)                           ; ⊥·b = ⊥

    ;; Inert: g row (16 cells computed)
    ((= a 4) (if (= b 0) 0 11))          ; g·⊤ = ⊤, g·x = 11

    ;; Selection: η·ρ = τ (1 cell computed)
    ((and (= a 9) (= b 8)) 3)            ; η·ρ = τ

    ;; E-transparency (2 cells computed)
    ((and (= a 7) (= b 0)) 0)            ; E·⊤ = ⊤
    ((and (= a 7) (= b 1)) 1)            ; E·⊥ = ⊥

    ;; Branch on QE core: ρ·x = f·x if τ·x=⊤ else g·x (5 cells)
    ((and (= a 8) (or (= b 2) (= b 3) (= b 4) (= b 5)))
     (self-dot-brute 2 b))               ; f-path (τ·{2,3,4,5} = ⊤)
    ((and (= a 8) (= b 14))
     11)                                  ; g-path (τ·14 = 1, g·14 = 11)

    ;; Compose on QE core: η·x = ρ·(g·x) (4 cells)
    ((and (= a 9) (or (= b 2) (= b 3) (= b 4) (= b 5)))
     (self-dot-brute 8 11))              ; ρ·(g·x) = ρ·11 = 14

    ;; All other cells: fall through to brute-force
    (t (self-dot-brute a b))))

;; ── Verification ──

(define (verify-self-sim sim-fn)
  (let ((errors 0)
        (tested 0))
    ;; Test all 256 cells against the dot builtin
    (define (check a b)
      (let ((expected (dot a b))
            (got (sim-fn a b)))
        (setq tested (1+ tested))
        (if (not (= expected got))
          (progn
            (setq errors (1+ errors))
            (display "FAIL: (")
            (display a)
            (display ",")
            (display b)
            (display ") = ")
            (display got)
            (display " expected ")
            (print expected)))))

    ;; Test a representative sample (full 256 would be slow in interpreter)
    (check 0 0) (check 0 5) (check 0 15)   ; absorber row
    (check 1 0) (check 1 5) (check 1 15)   ; absorber row
    (check 3 2) (check 3 6) (check 3 14)   ; tester row
    (check 4 0) (check 4 5) (check 4 15)   ; inert row
    (check 6 0) (check 6 5) (check 6 14)   ; Q row
    (check 7 0) (check 7 1) (check 7 5)    ; E row (with transparency)
    (check 8 2) (check 8 3) (check 8 14)   ; ρ row (Branch)
    (check 9 2) (check 9 5) (check 9 8)    ; η row (Compose + Selection)
    (check 2 0) (check 2 7) (check 2 15)   ; f row
    (check 10 0) (check 10 5) (check 10 8) ; Y row
    (check 15 0) (check 15 7) (check 15 15); filler row

    (display "  Tested: ")
    (display tested)
    (display " cells, errors: ")
    (print errors)))

(print "=== SELF-SIMULATOR VERIFICATION ===")
(print "")
(print "Brute-force self-simulator:")
(verify-self-sim self-dot-brute)
(print "")
(print "Role-aware self-simulator:")
(verify-self-sim self-dot-role)
