; psi_recovery_spell.lisp — Pure Ψ-Lisp black-box recovery
;
; Translates recover_adaptive (psi_blackbox.py) into pure Lisp.
; Communicates only through IO atoms: (put x) and (get).
;
; IO Protocol:
;   PROBE:  (put 0) (put a) (put b) (get) → dot(a,b)
;   REPORT: (put 1) (put idx) (put label)
;   STATUS: (put 2) (put phase-code)       — evaluation snapshot
;
; Expects `domain` bound in env (list of 16 opaque labels).
; Returns an association list ((0 . top) (1 . bot) ... (15 . dec)).

;; ── List helpers ──────────────────────────────────────────────────────

(defun member (x lst)
  (if (null lst) NIL
    (if (= x (car lst)) T
      (member x (cdr lst)))))

(defun length (lst)
  (if (null lst) 0
    (+ 1 (length (cdr lst)))))

(defun nth (n lst)
  (if (= n 0) (car lst)
    (nth (- n 1) (cdr lst))))

(defun append (a b)
  (if (null a) b
    (cons (car a) (append (cdr a) b))))

(defun remove (x lst)
  (if (null lst) NIL
    (if (= x (car lst))
      (remove x (cdr lst))
      (cons (car lst) (remove x (cdr lst))))))

(defun filter-not-in (lst exclusions)
  ;; Return elements of lst not in exclusions
  (if (null lst) NIL
    (if (member (car lst) exclusions)
      (filter-not-in (cdr lst) exclusions)
      (cons (car lst) (filter-not-in (cdr lst) exclusions)))))

;; ── IO wrappers ──────────────────────────────────────────────────────

(defun probe (a b)
  (put 0) (put a) (put b) (get))

(defun report (idx label)
  (put 1) (put idx) (put label))

(defun status (phase)
  (put 2) (put phase))

;; ── Phase 1: Idempotent scan (16 probes) ─────────────────────────────
;; Only ⊤ and ⊥ satisfy dot(x,x) = x.

(defun find-idempotents (lst)
  (if (null lst) NIL
    (let ((x (car lst))
          (xx (probe (car lst) (car lst))))
      (if (= xx x)
        (cons x (find-idempotents (cdr lst)))
        (find-idempotents (cdr lst))))))

;; ── Phase 2: Absorber-probe signatures (28 probes) ───────────────────
;; For each non-absorber x, compute (x·abs_a, x·abs_b) and classify.

(defun classify-loop (lst abs-a abs-b full-pres semi-a semi-b swap-a swap-b)
  ;; Walk lst, accumulate into 5 bins. Return (full-pres semi-a semi-b swap-a swap-b).
  (if (null lst)
    (list full-pres semi-a semi-b swap-a swap-b)
    (let ((x  (car lst))
          (va (probe (car lst) abs-a))
          (vb (probe (car lst) abs-b)))
      (if (and (= va abs-a) (= vb abs-b))
        ;; full preserver
        (classify-loop (cdr lst) abs-a abs-b
          (cons x full-pres) semi-a semi-b swap-a swap-b)
      (if (and (= va abs-a) (not (= vb abs-a)) (not (= vb abs-b)))
        ;; semi-a: preserves abs-a, non-absorber on abs-b
        (classify-loop (cdr lst) abs-a abs-b
          full-pres (cons x semi-a) semi-b swap-a swap-b)
      (if (and (= vb abs-b) (not (= va abs-a)) (not (= va abs-b)))
        ;; semi-b: preserves abs-b, non-absorber on abs-a
        (classify-loop (cdr lst) abs-a abs-b
          full-pres semi-a (cons x semi-b) swap-a swap-b)
      (if (and (= vb abs-a) (not (= va abs-a)) (not (= va abs-b)))
        ;; swap-to-a: maps abs-b → abs-a
        (classify-loop (cdr lst) abs-a abs-b
          full-pres semi-a semi-b (cons x swap-a) swap-b)
      (if (and (= va abs-b) (not (= vb abs-a)) (not (= vb abs-b)))
        ;; swap-to-b: maps abs-a → abs-b
        (classify-loop (cdr lst) abs-a abs-b
          full-pres semi-a semi-b swap-a (cons x swap-b))
        ;; else: skip (shouldn't happen in Ψ₁₆)
        (classify-loop (cdr lst) abs-a abs-b
          full-pres semi-a semi-b swap-a swap-b)))))))))

;; ── Phase 4: Find E among full preservers (1-4 probes) ──────────────
;; E is the unique encoder — probing it on a non-absorber/non-full-preserver
;; yields a non-absorber result.

(defun find-E (candidates test-elem abs-a abs-b)
  (if (null candidates) NIL
    (let ((x (car candidates))
          (v (probe (car candidates) test-elem)))
      (if (and (not (= v abs-a)) (not (= v abs-b)))
        x
        (find-E (cdr candidates) test-elem abs-a abs-b)))))

;; ── Phase 5: Find Q among swap candidates (2-6 probes) ──────────────
;; Q is the unique element where E·(Q·E) = Q.

(defun find-Q (candidates big-E)
  (if (null candidates) NIL
    (let ((x  (car candidates))
          (qe (probe (car candidates) big-E)))
      (if (= (probe big-E qe) x)
        x
        (find-Q (cdr candidates) big-E)))))

;; ── Main recovery ────────────────────────────────────────────────────

(defun recover (dom)
  (status 0)  ; scanning idempotents
  (let ((absorbers (find-idempotents dom)))
    (let ((abs-a (nth 0 absorbers))
          (abs-b (nth 1 absorbers))
          (non-abs (filter-not-in dom absorbers)))
      (status 1)  ; classifying by absorber signatures
      (let ((bins (classify-loop non-abs abs-a abs-b NIL NIL NIL NIL NIL)))
        (let ((full-pres (nth 0 bins))
              (semi-a    (nth 1 bins))
              (semi-b    (nth 2 bins))
              (swap-a    (nth 3 bins))
              (swap-b    (nth 4 bins)))
          (status 2)  ; orienting absorbers
          (let ((top        (if (= (length semi-a) 1) abs-a abs-b))
                (bot        (if (= (length semi-a) 1) abs-b abs-a))
                (q-cands    (if (= (length semi-a) 1) swap-a swap-b))
                (test-pool  (filter-not-in non-abs full-pres)))
            (status 3)  ; finding E via Kleene test
            (let ((big-E (find-E full-pres (car test-pool) top bot)))
              (status 4)  ; finding Q via QE round-trip
              (let ((big-Q (find-Q q-cands big-E)))
                (status 5)  ; generating depth-1 elements
                (let ((f-val    (probe big-E big-E))
                      (pair-val (probe big-E big-Q))
                      (s1-val   (probe big-Q big-Q))
                      (dec-val  (probe big-Q top)))
                  (status 6)  ; generating depth-2 elements
                  (let ((tau-val (probe f-val s1-val))
                        (g-val   (probe pair-val dec-val))
                        (seq-val (probe f-val top))
                        (rho-val (probe f-val big-E))
                        (eta-val (probe f-val pair-val))
                        (y-val   (probe pair-val s1-val))
                        (s0-val  (probe big-Q s1-val))
                        (inc-val (probe f-val f-val)))
                    ;; Report all 16 identifications
                    (report  0 top)       ; ⊤
                    (report  1 bot)       ; ⊥
                    (report  2 f-val)     ; f
                    (report  3 tau-val)   ; τ
                    (report  4 g-val)     ; g
                    (report  5 seq-val)   ; SEQ
                    (report  6 big-Q)     ; Q
                    (report  7 big-E)     ; E
                    (report  8 rho-val)   ; ρ
                    (report  9 eta-val)   ; η
                    (report 10 y-val)     ; Y
                    (report 11 pair-val)  ; PAIR
                    (report 12 s0-val)    ; s0
                    (report 13 inc-val)   ; INC
                    (report 14 s1-val)    ; s1
                    (report 15 dec-val)   ; DEC
                    ;; Return assoc list
                    (list
                      (cons  0 top)
                      (cons  1 bot)
                      (cons  2 f-val)
                      (cons  3 tau-val)
                      (cons  4 g-val)
                      (cons  5 seq-val)
                      (cons  6 big-Q)
                      (cons  7 big-E)
                      (cons  8 rho-val)
                      (cons  9 eta-val)
                      (cons 10 y-val)
                      (cons 11 pair-val)
                      (cons 12 s0-val)
                      (cons 13 inc-val)
                      (cons 14 s1-val)
                      (cons 15 dec-val))))))))))))

;; ── Entry point ──────────────────────────────────────────────────────
;; `domain` is injected by the runtime.
(recover domain)
