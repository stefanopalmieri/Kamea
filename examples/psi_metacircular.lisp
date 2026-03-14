;;;; psi_metacircular.lisp — CPS Meta-Circular Evaluator for Ψ-Lisp
;;;;
;;;; A Ψ-Lisp interpreter written in Ψ-Lisp with explicit continuations.
;;;; Follows Smith's 3-Lisp (1984) and Reynolds' definitional interpreters (1972).
;;;;
;;;; Every evaluation step takes a continuation k — a lambda that receives
;;;; the result. This makes control flow explicit and reifiable. The evaluator
;;;; is a state machine: (expr, env, k) → (expr', env', k').
;;;;
;;;; Reify/reflect are cases in the evaluator, not builtins. Reify packages
;;;; the current state (continuation + environment) as data. Reflect installs
;;;; a (possibly modified) state, abandoning the current continuation.
;;;;
;;;; Architecture:
;;;;   Layer 3: User program (e.g., fib 8)
;;;;            ↓ interpreted by
;;;;   Layer 2: This CPS evaluator (psi_metacircular.lisp)
;;;;            ↓ interpreted by
;;;;   Layer 1: Base evaluator (psi_lisp.py)
;;;;            ↓ executes via
;;;;   Layer 0: Cayley table (256 bytes)

;;; ── Tags for meta-level values ──────────────────────────────────────
;;; Small numbers to avoid deep Q-chains (Python __eq__ is recursive).

(setq CLOSURE-TAG 90)
(setq BUILTIN-TAG 91)

;;; ── Association list operations ─────────────────────────────────────

(defun m-assoc (key alist)
  "Find (key . val) pair in alist."
  (if (null alist) NIL
    (if (= key (car (car alist)))
      (car alist)
      (m-assoc key (cdr alist)))))

(defun m-lookup (sym menv)
  "Look up sym in environment alist."
  (let ((pair (m-assoc sym menv)))
    (if (null pair) NIL (cdr pair))))

(defun extend-env (params args menv)
  "Extend env by zipping params with args."
  (if (null params) menv
    (cons (cons (car params) (car args))
          (extend-env (cdr params) (cdr args) menv))))

;;; ── Closure constructors/accessors ──────────────────────────────────

(defun make-closure (name params body cenv)
  (list CLOSURE-TAG name params body cenv))

(defun closurep (x)
  (if (null x) NIL
    (if (numberp x) NIL
      (if (= x T) NIL
        (= (car x) CLOSURE-TAG)))))

(defun closure-name   (c) (car (cdr c)))
(defun closure-params (c) (car (cdr (cdr c))))
(defun closure-body   (c) (car (cdr (cdr (cdr c)))))
(defun closure-env    (c) (car (cdr (cdr (cdr (cdr c))))))

;;; ── Builtin constructors/accessors ──────────────────────────────────

(defun make-builtin (name) (list BUILTIN-TAG name))

(defun builtinp (x)
  (if (null x) NIL
    (if (numberp x) NIL
      (if (= x T) NIL
        (= (car x) BUILTIN-TAG)))))

(defun builtin-name (b) (car (cdr b)))

;;; ── Builtin dispatch ────────────────────────────────────────────────

(defun apply-builtin (name args)
  (cond
    ((= name '+)       (+ (car args) (car (cdr args))))
    ((= name '-)       (- (car args) (car (cdr args))))
    ((= name '*)       (* (car args) (car (cdr args))))
    ((= name '<)       (< (car args) (car (cdr args))))
    ((= name '>)       (> (car args) (car (cdr args))))
    ((= name '=)       (= (car args) (car (cdr args))))
    ((= name 'cons)    (cons (car args) (car (cdr args))))
    ((= name 'car)     (car (car args)))
    ((= name 'cdr)     (cdr (car args)))
    ((= name 'null)    (null (car args)))
    ((= name 'numberp) (numberp (car args)))
    ((= name 'print)   (print (car args)))
    ((= name 'list)    args)
    ((= name 'not)     (if (null (car args)) T NIL))
    (T NIL)))

;;; ── Expression predicates ───────────────────────────────────────────
;;; Convention: numbers < 100 are self-evaluating, >= 100 are symbol IDs.

(defun self-eval? (expr)
  (if (null expr) T
    (if (= expr T) T
      (if (numberp expr) (< expr 100) NIL))))

(defun symbol? (expr)
  (if (numberp expr) (not (< expr 100)) NIL))

(defun compound? (expr)
  (not (or (null expr) (= expr T) (numberp expr))))

;;; ── The CPS Evaluator ───────────────────────────────────────────────

(defun meval (expr menv k)
  "Evaluate expr in menv, passing result to continuation k."
  (cond
    ;; Self-evaluating: NIL, T, numbers < 100
    ((null expr)        (k NIL))
    ((= expr T)         (k T))
    ((self-eval? expr)  (k expr))

    ;; Symbol lookup
    ((symbol? expr)     (k (m-lookup expr menv)))

    ;; Compound expression
    ((compound? expr)
      (let ((head (car expr)))
        (cond
          ;; (quote datum)
          ((= head 'quote)
            (k (car (cdr expr))))

          ;; (if test then else)
          ((= head 'if)
            (meval (car (cdr expr)) menv
              (lambda (tv)
                (if (null tv)
                  (if (null (cdr (cdr (cdr expr)))) (k NIL)
                    (meval (car (cdr (cdr (cdr expr)))) menv k))
                  (meval (car (cdr (cdr expr))) menv k)))))

          ;; (cond (test val) ...)
          ((= head 'cond)
            (eval-cond (cdr expr) menv k))

          ;; (lambda (params) body)
          ((= head 'lambda)
            (k (make-closure NIL (car (cdr expr)) (car (cdr (cdr expr))) menv)))

          ;; (let ((x v) ...) body)
          ((= head 'let)
            (eval-let-bindings (car (cdr expr)) menv
              (lambda (new-env)
                (meval (car (cdr (cdr expr))) new-env k))))

          ;; (progn expr ...)
          ((= head 'progn)
            (eval-sequence (cdr expr) menv k))

          ;; ── REIFY ──────────────────────────────────────────
          ;; The 3-Lisp move: capture the current continuation and
          ;; environment as a first-class value. The program receives
          ;; its own future as data.
          ;;
          ;; Returns: (reified-state <continuation> <environment> <expression>)
          ;; The continuation is a host-level lambda — opaque but callable.
          ;; The environment is a cons-list alist — fully inspectable.
          ((= head 'reify)
            (k (list 'reified-state k menv expr)))

          ;; ── REFLECT ────────────────────────────────────────
          ;; Install a (possibly modified) state. Abandons the current
          ;; continuation and jumps to the one in the reified state.
          ;; (reflect state value) — eval state, eval value, jump.
          ((= head 'reflect)
            (meval (car (cdr expr)) menv
              (lambda (state)
                (meval (car (cdr (cdr expr))) menv
                  (lambda (val)
                    ;; state = (reified-state k env expr)
                    (let ((saved-k (car (cdr state))))
                      (saved-k val)))))))

          ;; Function application: (fn arg1 arg2 ...)
          (T
            (meval head menv
              (lambda (fn)
                (eval-args (cdr expr) menv
                  (lambda (args)
                    (mapply fn args k)))))))))

    ;; Fallback
    (T (k expr))))

;;; ── CPS helpers ─────────────────────────────────────────────────────

(defun mapply (fn args k)
  "Apply fn to args, passing result to continuation k."
  (cond
    ((closurep fn)
      (let ((call-env (extend-env (closure-params fn) args (closure-env fn))))
        ;; If named (from defun), bind self for recursion
        (let ((final-env (if (null (closure-name fn)) call-env
                           (cons (cons (closure-name fn) fn) call-env))))
          (meval (closure-body fn) final-env k))))
    ((builtinp fn)
      (k (apply-builtin (builtin-name fn) args)))
    (T (k NIL))))

(defun eval-args (exprs menv k)
  "Evaluate argument list left-to-right, pass results to k."
  (if (null exprs) (k NIL)
    (meval (car exprs) menv
      (lambda (val)
        (eval-args (cdr exprs) menv
          (lambda (rest)
            (k (cons val rest))))))))

(defun eval-cond (clauses menv k)
  "Evaluate cond clauses in order."
  (if (null clauses) (k NIL)
    (meval (car (car clauses)) menv
      (lambda (tv)
        (if (null tv)
          (eval-cond (cdr clauses) menv k)
          (meval (car (cdr (car clauses))) menv k))))))

(defun eval-let-bindings (bindings menv k)
  "Evaluate let bindings, extending env, then call k with new env."
  (if (null bindings) (k menv)
    (meval (car (cdr (car bindings))) menv
      (lambda (val)
        (eval-let-bindings (cdr bindings)
          (cons (cons (car (car bindings)) val) menv)
          k)))))

(defun eval-sequence (exprs menv k)
  "Evaluate a sequence, return last result."
  (if (null (cdr exprs))
    (meval (car exprs) menv k)
    (meval (car exprs) menv
      (lambda (ignored)
        (eval-sequence (cdr exprs) menv k)))))

;;; ── Top-level program evaluation (handles defun) ────────────────────

(defun defun-form? (expr)
  (if (compound? expr) (= (car expr) 'defun) NIL))

(defun meval-toplevel (expr menv k)
  "Evaluate top-level form. k receives (val new-env)."
  (if (defun-form? expr)
    ;; (defun name (params) body) — create recursive closure
    (let ((name (car (cdr expr)))
          (params (car (cdr (cdr expr))))
          (body (car (cdr (cdr (cdr expr))))))
      (let ((closure (make-closure name params body menv)))
        (let ((new-env (cons (cons name closure) menv)))
          ;; Rebuild closure with env that includes itself (for recursion)
          (let ((rec-closure (make-closure name params body new-env)))
            (let ((final-env (cons (cons name rec-closure) menv)))
              (k rec-closure final-env))))))
    ;; Regular expression
    (meval expr menv (lambda (val) (k val menv)))))

(defun meval-program (exprs menv k)
  "Evaluate a list of top-level forms, threading env through defuns."
  (if (null exprs) (k NIL)
    (meval-toplevel (car exprs) menv
      (lambda (val new-env)
        (if (null (cdr exprs)) (k val)
          (meval-program (cdr exprs) new-env k))))))

;;; ── Base environment ────────────────────────────────────────────────

(defun make-base-env ()
  (list
    (cons '+ (make-builtin '+))
    (cons '- (make-builtin '-))
    (cons '* (make-builtin '*))
    (cons '< (make-builtin '<))
    (cons '> (make-builtin '>))
    (cons '= (make-builtin '=))
    (cons 'cons (make-builtin 'cons))
    (cons 'car (make-builtin 'car))
    (cons 'cdr (make-builtin 'cdr))
    (cons 'null (make-builtin 'null))
    (cons 'numberp (make-builtin 'numberp))
    (cons 'print (make-builtin 'print))
    (cons 'list (make-builtin 'list))
    (cons 'not (make-builtin 'not))))

;; Identity continuation — the top of the tower
(defun id (x) x)

;; Convenience: count entries in an alist
(defun m-length (lst)
  (if (null lst) 0 (+ 1 (m-length (cdr lst)))))
