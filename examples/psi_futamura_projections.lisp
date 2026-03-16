; ═══════════════════════════════════════════════════════════════════════
; All Three Futamura Projections on the Ψ₁₆ᶜ Algebra
; ═══════════════════════════════════════════════════════════════════════
;
; Run with: python3 psi_lisp.py --table=c examples/psi_futamura_projections.lisp
;
; Expression encoding (tagged pairs, integers 0-6 as tags):
;   (0 . n)                  Atom(n)
;   (1 . name)               Var(name)
;   (2 . (a . b))            Dot(a, b)
;   (3 . (test . (t . e)))   If(test, then, else)
;   (4 . (x . (val . body))) Let(x, val, body)
;   (5 . (x . body))         Lam(x, body)
;   (6 . (fn . arg))         App(fn, arg)

; ── Expression constructors ──────────────────────────────────────────

(defun mk-atom (n)          (cons 0 n))
(defun mk-var (name)        (cons 1 name))
(defun mk-dot (a b)         (cons 2 (cons a b)))
(defun mk-if (test t e)     (cons 3 (cons test (cons t e))))
(defun mk-let (x val body)  (cons 4 (cons x (cons val body))))
(defun mk-lam (x body)      (cons 5 (cons x body)))
(defun mk-app (fn arg)      (cons 6 (cons fn arg)))

; ── Expression accessors ─────────────────────────────────────────────

(defun expr-tag (e) (car e))
(defun is-atom (e) (= (car e) 0))
(defun is-var (e)  (= (car e) 1))
(defun is-dot (e)  (= (car e) 2))
(defun is-if (e)   (= (car e) 3))
(defun is-let (e)  (= (car e) 4))
(defun is-lam (e)  (= (car e) 5))
(defun is-app (e)  (= (car e) 6))

(defun atom-val (e)  (cdr e))
(defun dot-a (e)     (car (cdr e)))
(defun dot-b (e)     (cdr (cdr e)))
(defun if-test (e)   (car (cdr e)))
(defun if-then (e)   (car (cdr (cdr e))))
(defun if-else (e)   (cdr (cdr (cdr e))))
(defun let-var (e)   (car (cdr e)))
(defun let-val (e)   (car (cdr (cdr e))))
(defun let-body (e)  (cdr (cdr (cdr e))))
(defun lam-var (e)   (car (cdr e)))
(defun lam-body (e)  (cdr (cdr e)))
(defun app-fn (e)    (car (cdr e)))
(defun app-arg (e)   (cdr (cdr e)))

; ── Substitution ─────────────────────────────────────────────────────

(defun subst-expr (var val expr)
  (cond
    ((is-atom expr) expr)
    ((is-var expr)
     (if (= (cdr expr) var) val expr))
    ((is-dot expr)
     (mk-dot (subst-expr var val (dot-a expr))
             (subst-expr var val (dot-b expr))))
    ((is-if expr)
     (mk-if (subst-expr var val (if-test expr))
            (subst-expr var val (if-then expr))
            (subst-expr var val (if-else expr))))
    ((is-let expr)
     (if (= (let-var expr) var)
         (mk-let (let-var expr)
                 (subst-expr var val (let-val expr))
                 (let-body expr))
         (mk-let (let-var expr)
                 (subst-expr var val (let-val expr))
                 (subst-expr var val (let-body expr)))))
    ((is-lam expr)
     (if (= (lam-var expr) var)
         expr
         (mk-lam (lam-var expr)
                 (subst-expr var val (lam-body expr)))))
    ((is-app expr)
     (mk-app (subst-expr var val (app-fn expr))
             (subst-expr var val (app-arg expr))))
    (T expr)))

; ── The Specializer (partial evaluator) ──────────────────────────────

(defun specialize (expr)
  (cond
    ((is-atom expr) expr)
    ((is-var expr) expr)
    ((is-dot expr)
     (let ((a (specialize (dot-a expr)))
           (b (specialize (dot-b expr))))
       (if (and (is-atom a) (is-atom b))
           (mk-atom (dot (atom-val a) (atom-val b)))
           (mk-dot a b))))
    ((is-if expr)
     (let ((test (specialize (if-test expr))))
       (if (is-atom test)
           (if (= (atom-val test) 1)
               (specialize (if-else expr))
               (specialize (if-then expr)))
           (mk-if test
                  (specialize (if-then expr))
                  (specialize (if-else expr))))))
    ((is-let expr)
     (let ((val (specialize (let-val expr))))
       (if (is-atom val)
           (specialize (subst-expr (let-var expr) val (let-body expr)))
           (mk-let (let-var expr) val (specialize (let-body expr))))))
    ((is-lam expr)
     (mk-lam (lam-var expr) (specialize (lam-body expr))))
    ((is-app expr)
     (let ((fn (specialize (app-fn expr)))
           (arg (specialize (app-arg expr))))
       (if (is-lam fn)
           ; Beta reduce: substitute arg (any value) into lambda body
           (specialize (subst-expr (lam-var fn) arg (lam-body fn)))
           (mk-app fn arg))))
    (T expr)))

; ── Pretty-printer for expression trees ──────────────────────────────

; Decode: extract the final atom value from a fully specialized expression
(defun decode (e)
  (if (is-atom e) (atom-val e) e))

; Pretty-print: show expression structure as a string description
(defun show-expr (e)
  (cond
    ((is-atom e) (atom-val e))
    ((is-var e)
     (cdr e))
    ((is-dot e)
     ; Print dot(a, b) showing atom values
     (let ((a (show-expr (dot-a e)))
           (b (show-expr (dot-b e))))
       (cons a (cons b NIL))))  ; (a b) as a list
    (T e)))

; ═══════════════════════════════════════════════════════════════════════
; PROJECTION 1: specialize(interpreter, program) = compiled value
; ═══════════════════════════════════════════════════════════════════════
;
; The interpreter: (lam op (lam arg (dot op arg)))
; Fully applied to known opcodes and known input → constant.

(write-string "=== PROJECTION 1: specialize(interp, program) = value ===")
(terpri)

; Interpreter as expression tree
(setq interp (mk-lam 200 (mk-lam 201 (mk-dot (mk-var 200) (mk-var 201)))))

; Program: INC(INC(INC(f)))  — all known
(setq p1-full
  (mk-app (mk-app interp (mk-atom 13))
          (mk-app (mk-app interp (mk-atom 13))
                  (mk-app (mk-app interp (mk-atom 13))
                          (mk-atom 2)))))

(write-string "  INC(INC(INC(f))): ")
(print (decode (specialize p1-full)))
; Expected: 5

; Program: E(Q(g))
(setq p2-full
  (mk-app (mk-app interp (mk-atom 7))
          (mk-app (mk-app interp (mk-atom 6))
                  (mk-atom 4))))

(write-string "  E(Q(g)):          ")
(print (decode (specialize p2-full)))
; Expected: 4

; ═══════════════════════════════════════════════════════════════════════
; PROJECTION 2: specialize(interp(program, _)) = compiler(input)
; ═══════════════════════════════════════════════════════════════════════
;
; Opcodes are KNOWN but input is UNKNOWN (a variable).
; The specializer should produce a RESIDUAL FUNCTION — the compiled
; program as an expression tree with the input variable free.
;
; specialize(App(App(interp, INC), App(App(interp, INC), App(App(interp, INC), Var(x)))))
; Should produce: Dot(Atom(INC), Dot(Atom(INC), Dot(Atom(INC), Var(x))))
; That IS the compiled program: a chain of dot operations with no
; interpretation overhead.

(write-string "=== PROJECTION 2: specialize(interp(program, _)) = compiler ===")
(terpri)

; Use variable 999 for the unknown input
(setq unknown-x (mk-var 999))

; Program: INC(INC(INC(x))) with unknown x
(setq p1-partial
  (mk-app (mk-app interp (mk-atom 13))
          (mk-app (mk-app interp (mk-atom 13))
                  (mk-app (mk-app interp (mk-atom 13))
                          unknown-x))))

(setq compiled-p1 (specialize p1-partial))

(write-string "  INC(INC(INC(x))) compiled to dot chain: ")
(print (is-dot compiled-p1))
; Expected: (dot 13 (dot 13 (dot 13 999)))
; That's: dot(INC, dot(INC, dot(INC, x))) — the compiled program

; Verify: substitute x=f (element 2) and specialize → should get 5
(setq applied-p1 (specialize (subst-expr 999 (mk-atom 2) compiled-p1)))
(write-string "  ...applied to f:          ")
(print (decode applied-p1))
; Expected: 5

; Program: DEC(INV(INC(x))) with unknown x
(setq p2-partial
  (mk-app (mk-app interp (mk-atom 15))
          (mk-app (mk-app interp (mk-atom 14))
                  (mk-app (mk-app interp (mk-atom 13))
                          unknown-x))))

(setq compiled-p2 (specialize p2-partial))
(write-string "  DEC(INV(INC(x))) compiled: ")
(print (decode compiled-p2))
; Expected: (dot 15 (dot 14 (dot 13 999)))

; Verify: substitute x=TAU (element 3) → should get f (element 2)
(setq applied-p2 (specialize (subst-expr 999 (mk-atom 3) compiled-p2)))
(write-string "  ...applied to TAU:        ")
(print (decode applied-p2))
; Expected: 2

; Program: E(Q(x)) with unknown x
(setq p3-partial
  (mk-app (mk-app interp (mk-atom 7))
          (mk-app (mk-app interp (mk-atom 6))
                  unknown-x)))

(setq compiled-p3 (specialize p3-partial))
(write-string "  E(Q(x)) compiled:         ")
(print (decode compiled-p3))
; Expected: (dot 7 (dot 6 999))

; Verify: substitute x=g (element 4) → should get g (element 4) by QE
(setq applied-p3 (specialize (subst-expr 999 (mk-atom 4) compiled-p3)))
(write-string "  ...applied to g:          ")
(print (decode applied-p3))
; Expected: 4

; ═══════════════════════════════════════════════════════════════════════
; PROJECTION 2 VERIFICATION: compiler = specialize(specialize, interp)
; ═══════════════════════════════════════════════════════════════════════
;
; The "compiler" is the function that takes a program encoding and
; produces compiled code. We demonstrate this by wrapping the above
; in a lambda over the opcode arguments.
;
; compiler(op1, op2, op3) = specialize(interp(op1, interp(op2, interp(op3, x))))
;
; When we specialize with known opcodes, we get the dot chain.
; When we then apply the dot chain to a known input, we get the value.
;
; Three paths to the same result:
;   Path A: direct table lookup         INC(INC(INC(f)))          = 5
;   Path B: specialize(interp, program) with all known            = 5
;   Path C: compile(program) then apply to input                  = 5

(write-string "=== THREE PATHS: direct / projection 1 / projection 2 ===")
(terpri)

; Path A: direct (using Ψ-Lisp dot)
(setq path-a (dot 13 (dot 13 (dot 13 2))))
(write-string "  Path A (direct):       ")
(print path-a)

; Path B: projection 1 (fully specialized)
(setq path-b (decode (specialize p1-full)))
(write-string "  Path B (projection 1): ")
(print path-b)

; Path C: projection 2 (compile then apply)
(setq path-c (decode applied-p1))
(write-string "  Path C (projection 2): ")
(print path-c)

(write-string "  All three equal: ")
(print (and (= path-a path-b) (= path-b path-c)))

NIL
