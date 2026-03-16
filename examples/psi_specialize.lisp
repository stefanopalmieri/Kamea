; ═══════════════════════════════════════════════════════════════════════
; Ψ∗ Specializer — a partial evaluator written in Ψ-Lisp
; ═══════════════════════════════════════════════════════════════════════
;
; Expression encoding (tagged pairs):
;   Atom(n)           → (0 . n)
;   Var(name)         → (1 . name)
;   Dot(a, b)         → (2 . (a . b))
;   If(test, t, e)    → (3 . (test . (t . e)))
;   Let(x, val, body) → (4 . (x . (val . body)))
;   Lam(x, body)      → (5 . (x . body))
;   App(fn, arg)      → (6 . (fn . arg))
;
; Tags are integers 0-6, not algebraic elements. This avoids
; confusion between the tags and the values being manipulated.
;
; Usage:
;   python3 psi_lisp.py examples/psi_specialize.lisp
; ═══════════════════════════════════════════════════════════════════════

; ── Expression constructors ──────────────────────────────────────────

(defun mk-atom (n)       (cons 0 n))
(defun mk-var (name)     (cons 1 name))
(defun mk-dot (a b)      (cons 2 (cons a b)))
(defun mk-if (test t e)  (cons 3 (cons test (cons t e))))
(defun mk-let (x val body) (cons 4 (cons x (cons val body))))
(defun mk-lam (x body)   (cons 5 (cons x body)))
(defun mk-app (fn arg)   (cons 6 (cons fn arg)))

; ── Expression accessors ─────────────────────────────────────────────

(defun expr-tag (e)   (car e))
(defun expr-payload (e) (cdr e))

; For Dot(a, b): payload = (a . b)
(defun dot-a (e) (car (cdr e)))
(defun dot-b (e) (cdr (cdr e)))

; For If(test, t, e): payload = (test . (t . e))
(defun if-test (e) (car (cdr e)))
(defun if-then (e) (car (cdr (cdr e))))
(defun if-else (e) (cdr (cdr (cdr e))))

; For Let(x, val, body): payload = (x . (val . body))
(defun let-var (e)  (car (cdr e)))
(defun let-val (e)  (car (cdr (cdr e))))
(defun let-body (e) (cdr (cdr (cdr e))))

; For Lam(x, body): payload = (x . body)
(defun lam-var (e)  (car (cdr e)))
(defun lam-body (e) (cdr (cdr e)))

; For App(fn, arg): payload = (fn . arg)
(defun app-fn (e)  (car (cdr e)))
(defun app-arg (e) (cdr (cdr e)))

; ── Predicates ───────────────────────────────────────────────────────

(defun is-atom (e) (= (expr-tag e) 0))
(defun is-var (e)  (= (expr-tag e) 1))
(defun is-dot (e)  (= (expr-tag e) 2))
(defun is-if (e)   (= (expr-tag e) 3))
(defun is-let (e)  (= (expr-tag e) 4))
(defun is-lam (e)  (= (expr-tag e) 5))
(defun is-app (e)  (= (expr-tag e) 6))

; ── Substitution: replace variable name with value in expression ─────

(defun subst-expr (var val expr)
  (cond
    ((is-atom expr) expr)
    ((is-var expr)
     (if (= (expr-payload expr) var)
         val
         expr))
    ((is-dot expr)
     (mk-dot (subst-expr var val (dot-a expr))
             (subst-expr var val (dot-b expr))))
    ((is-if expr)
     (mk-if (subst-expr var val (if-test expr))
            (subst-expr var val (if-then expr))
            (subst-expr var val (if-else expr))))
    ((is-let expr)
     (if (= (let-var expr) var)
         ; shadowed — only substitute in the val, not the body
         (mk-let (let-var expr)
                 (subst-expr var val (let-val expr))
                 (let-body expr))
         (mk-let (let-var expr)
                 (subst-expr var val (let-val expr))
                 (subst-expr var val (let-body expr)))))
    ((is-lam expr)
     (if (= (lam-var expr) var)
         expr  ; shadowed
         (mk-lam (lam-var expr)
                 (subst-expr var val (lam-body expr)))))
    ((is-app expr)
     (mk-app (subst-expr var val (app-fn expr))
             (subst-expr var val (app-arg expr))))
    (T expr)))

; ── The specializer (partial evaluator) ──────────────────────────────

(defun specialize (expr)
  (cond
    ; Atom — already a value
    ((is-atom expr) expr)

    ; Variable — can't reduce
    ((is-var expr) expr)

    ; Dot(a, b) — constant fold if both sides reduce to atoms
    ((is-dot expr)
     (let ((a (specialize (dot-a expr)))
           (b (specialize (dot-b expr))))
       (if (and (is-atom a) (is-atom b))
           ; Both atoms: look up the Cayley table
           (mk-atom (dot (expr-payload a) (expr-payload b)))
           ; Otherwise: residualize
           (mk-dot a b))))

    ; If — eliminate dead branch if test reduces to atom
    ((is-if expr)
     (let ((test (specialize (if-test expr))))
       (if (is-atom test)
           ; Known test: select branch
           ; BOT (1) = false, everything else = true
           (if (= (expr-payload test) 1)
               (specialize (if-else expr))
               (specialize (if-then expr)))
           ; Unknown test: residualize both branches
           (mk-if test
                  (specialize (if-then expr))
                  (specialize (if-else expr))))))

    ; Let — propagate known values
    ((is-let expr)
     (let ((val (specialize (let-val expr))))
       (if (is-atom val)
           ; Known value: substitute into body and specialize
           (specialize (subst-expr (let-var expr) val (let-body expr)))
           ; Unknown: residualize
           (mk-let (let-var expr) val (specialize (let-body expr))))))

    ; Lambda — specialize body
    ((is-lam expr)
     (mk-lam (lam-var expr) (specialize (lam-body expr))))

    ; App — beta reduce if function is a lambda
    ((is-app expr)
     (let ((fn (specialize (app-fn expr)))
           (arg (specialize (app-arg expr))))
       (if (is-lam fn)
           ; Beta reduce: substitute arg (any value) into lambda body
           (specialize (subst-expr (lam-var fn) arg (lam-body fn)))
           ; Otherwise: residualize
           (mk-app fn arg))))

    ; Fallback
    (T expr)))

; ── Helper: decode a result expression to show the atom value ────────

(defun decode (expr)
  (if (is-atom expr)
      (expr-payload expr)
      expr))

; ═══════════════════════════════════════════════════════════════════════
; TESTS
; ═══════════════════════════════════════════════════════════════════════

; ── Test 1: Constant folding ─────────────────────────────────────────
; (dot 13 12) = INC(SEQ) — should fold to a constant
; In Ψ₁₆ᶜ table: INC(12) = 3
(write-string "Test 1: dot(INC, SEQ) = ")
(print (decode (specialize (mk-dot (mk-atom 13) (mk-atom 12)))))

; ── Test 2: Nested dot — INC(INC(INC(f))) ───────────────────────────
; f=2, INC(2)=3, INC(3)=4, INC(4)=5
(write-string "Test 2: INC(INC(INC(f))) = ")
(print (decode (specialize
  (mk-dot (mk-atom 13)
          (mk-dot (mk-atom 13)
                  (mk-dot (mk-atom 13) (mk-atom 2)))))))

; ── Test 3: QE cancellation via table lookup ─────────────────────────
; E(Q(g)) = g (element 4) — the table lookup handles this
(write-string "Test 3: E(Q(g)) = ")
(print (decode (specialize
  (mk-dot (mk-atom 7) (mk-dot (mk-atom 6) (mk-atom 4))))))

; ── Test 4: Dead branch elimination ──────────────────────────────────
; (if TOP then else) → then. TOP = 0 (not BOT), so true branch
(write-string "Test 4: if(TOP, 42, 99) = ")
(print (decode (specialize
  (mk-if (mk-atom 0) (mk-atom 42) (mk-atom 99)))))

; ── Test 5: if(BOT, then, else) → else ──────────────────────────────
(write-string "Test 5: if(BOT, 42, 99) = ")
(print (decode (specialize
  (mk-if (mk-atom 1) (mk-atom 42) (mk-atom 99)))))

; ── Test 6: Let propagation ──────────────────────────────────────────
; (let x = INC in (dot x (atom 2))) → dot(INC, f) = INC(2) = 3
; Variable name 100 for x
(write-string "Test 6: let x=INC in dot(x, f) = ")
(print (decode (specialize
  (mk-let 100 (mk-atom 13)
          (mk-dot (mk-var 100) (mk-atom 2))))))

; ── Test 7: Beta reduction ───────────────────────────────────────────
; ((lam x (dot INC x)) f) → dot(INC, f) → INC(2) = 3
(write-string "Test 7: ((lam x (dot INC x)) f) = ")
(print (decode (specialize
  (mk-app (mk-lam 100 (mk-dot (mk-atom 13) (mk-var 100)))
          (mk-atom 2)))))

; ═══════════════════════════════════════════════════════════════════════
; FUTAMURA PROJECTION 1: specialize(interpreter, program)
; ═══════════════════════════════════════════════════════════════════════
;
; The opcode interpreter: (lam op (lam arg (dot op arg)))
; Encoded as an expression tree:
;   Lam(200, Lam(201, Dot(Var(200), Var(201))))
;
; A program: apply INC three times to f
; Encoded as: App(App(interp, INC), App(App(interp, INC), App(App(interp, INC), Atom(2))))

(write-string "--- Futamura Projection 1 ---")
(terpri)

; The interpreter as an expression
(setq interp (mk-lam 200 (mk-lam 201 (mk-dot (mk-var 200) (mk-var 201)))))

; The program: eval([INC, INC, INC], f)
(setq prog1
  (mk-app (mk-app interp (mk-atom 13))
          (mk-app (mk-app interp (mk-atom 13))
                  (mk-app (mk-app interp (mk-atom 13))
                          (mk-atom 2)))))

(write-string "Projection 1: specialize(eval([INC,INC,INC], f)) = ")
(print (decode (specialize prog1)))

; The program: eval([DEC, INV, INC], TAU)
(setq prog2
  (mk-app (mk-app interp (mk-atom 15))
          (mk-app (mk-app interp (mk-atom 14))
                  (mk-app (mk-app interp (mk-atom 13))
                          (mk-atom 3)))))

(write-string "Projection 1: specialize(eval([DEC,INV,INC], TAU)) = ")
(print (decode (specialize prog2)))

; The program: eval([E, Q], g) — QE round-trip
(setq prog3
  (mk-app (mk-app interp (mk-atom 7))
          (mk-app (mk-app interp (mk-atom 6))
                  (mk-atom 4))))

(write-string "Projection 1: specialize(eval([E,Q], g)) = ")
(print (decode (specialize prog3)))

NIL
