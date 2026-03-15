;;;; psi_metacircular.lisp — Defunctionalized CPS Meta-Circular Evaluator
;;;;
;;;; A Ψ-Lisp interpreter written in Ψ-Lisp with INSPECTABLE continuations.
;;;; Follows Smith's 3-Lisp (1984), Reynolds' definitional interpreters (1972),
;;;; and Danvy & Nielsen's defunctionalization at work (2001).
;;;;
;;;; Every continuation is a tagged data structure — a cons-list with a tag
;;;; symbol and captured values. No lambdas in the evaluator's control flow.
;;;; This means (reify) returns a fully inspectable state: the program can
;;;; walk the continuation chain, see what computation is pending, modify it,
;;;; and reflect into an altered future.
;;;;
;;;; Architecture:
;;;;   Layer 3: User program (e.g., fib 8)
;;;;            ↓ interpreted by
;;;;   Layer 2: This CPS evaluator (psi_metacircular.lisp)
;;;;            ↓ interpreted by
;;;;   Layer 1: Base evaluator (psi_lisp.py)
;;;;            ↓ executes via
;;;;   Layer 0: Cayley table (256 bytes)
;;;;
;;;; Continuation types (defunctionalized):
;;;;   k-id            — identity: return the final value
;;;;   k-if            — if-test evaluated, choose branch
;;;;   k-cond          — cond-test evaluated, choose clause
;;;;   k-let-body      — all let-bindings done, evaluate body
;;;;   k-let-bind      — one let-binding evaluated, continue binding
;;;;   k-seq           — sequence element done, evaluate next
;;;;   k-apply-fn      — function position evaluated, evaluate args
;;;;   k-do-apply      — all args evaluated, apply function
;;;;   k-args-head     — first arg evaluated, evaluate rest
;;;;   k-args-tail     — rest args evaluated, cons onto list
;;;;   k-reflect-state — reflect: state evaluated, evaluate value
;;;;   k-reflect-jump  — reflect: value evaluated, jump to saved-k
;;;;   k-top-wrap      — bridge: meval-toplevel → meval
;;;;   k-program-step  — bridge: meval-program threading

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
    ((= name 'nth)     (nth (car args) (car (cdr args))))
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

;;; ── List access helper ──────────────────────────────────────────────

(defun nth (n lst)
  "Return the nth element of lst (0-indexed)."
  (if (= n 0) (car lst)
    (nth (- n 1) (cdr lst))))

;;; ── Continuation Dispatch ───────────────────────────────────────────
;;; Every lambda from the original CPS evaluator is now a tagged list.
;;; apply-k dispatches on the tag and performs what the lambda would have.

(defun apply-k (k val)
  "Apply a defunctionalized continuation to a value."
  (let ((tag (car k)))
    (cond
      ;; ── k-id: identity continuation (top of chain) ──
      ;; ()
      ((= tag 'k-id)
        val)

      ;; ── k-if: if-test just evaluated ──
      ;; (k-if then-branch else-branch env next-k)
      ((= tag 'k-if)
        (let ((then-b (nth 1 k))
              (else-b (nth 2 k))
              (env    (nth 3 k))
              (next-k (nth 4 k)))
          (if (null val)
            (if (null else-b)
              (apply-k next-k NIL)
              (meval else-b env next-k))
            (meval then-b env next-k))))

      ;; ── k-cond: cond clause test just evaluated ──
      ;; (k-cond rest-clauses consequent env next-k)
      ((= tag 'k-cond)
        (let ((rest       (nth 1 k))
              (consequent (nth 2 k))
              (env        (nth 3 k))
              (next-k     (nth 4 k)))
          (if (null val)
            (eval-cond rest env next-k)
            (meval consequent env next-k))))

      ;; ── k-let-body: all let-bindings done, evaluate body ──
      ;; (k-let-body body next-k)
      ;; val = the extended environment
      ((= tag 'k-let-body)
        (let ((body   (nth 1 k))
              (next-k (nth 2 k)))
          (meval body val next-k)))

      ;; ── k-let-bind: one let-binding just evaluated ──
      ;; (k-let-bind var-name rest-bindings env next-k)
      ;; val = the value for this binding
      ((= tag 'k-let-bind)
        (let ((var-name (nth 1 k))
              (rest     (nth 2 k))
              (env      (nth 3 k))
              (next-k   (nth 4 k)))
          (eval-let-bindings rest
            (cons (cons var-name val) env)
            next-k)))

      ;; ── k-seq: sequence element just evaluated ──
      ;; (k-seq rest-exprs env next-k)
      ;; val = ignored (not the last element)
      ((= tag 'k-seq)
        (let ((rest   (nth 1 k))
              (env    (nth 2 k))
              (next-k (nth 3 k)))
          (eval-sequence rest env next-k)))

      ;; ── k-apply-fn: function position just evaluated ──
      ;; (k-apply-fn arg-exprs env next-k)
      ;; val = the evaluated function
      ((= tag 'k-apply-fn)
        (let ((arg-exprs (nth 1 k))
              (env       (nth 2 k))
              (next-k    (nth 3 k)))
          (eval-args arg-exprs env
            (list 'k-do-apply val next-k))))

      ;; ── k-do-apply: all arguments evaluated, apply function ──
      ;; (k-do-apply fn next-k)
      ;; val = the evaluated argument list
      ((= tag 'k-do-apply)
        (let ((fn     (nth 1 k))
              (next-k (nth 2 k)))
          (mapply fn val next-k)))

      ;; ── k-args-head: first arg just evaluated ──
      ;; (k-args-head rest-exprs env next-k)
      ;; val = the first evaluated argument
      ((= tag 'k-args-head)
        (let ((rest   (nth 1 k))
              (env    (nth 2 k))
              (next-k (nth 3 k)))
          (eval-args rest env
            (list 'k-args-tail val next-k))))

      ;; ── k-args-tail: remaining args just evaluated ──
      ;; (k-args-tail head-val next-k)
      ;; val = the evaluated rest of arguments
      ((= tag 'k-args-tail)
        (let ((head-val (nth 1 k))
              (next-k   (nth 2 k)))
          (apply-k next-k (cons head-val val))))

      ;; ── k-reflect-state: reflect state expression evaluated ──
      ;; (k-reflect-state value-expr env)
      ;; val = the reified state object
      ((= tag 'k-reflect-state)
        (let ((value-expr (nth 1 k))
              (env        (nth 2 k)))
          (meval value-expr env
            (list 'k-reflect-jump val))))

      ;; ── k-reflect-jump: reflect value evaluated, jump ──
      ;; (k-reflect-jump state)
      ;; val = the value to pass to the saved continuation
      ((= tag 'k-reflect-jump)
        (let ((state (nth 1 k)))
          (let ((saved-k (car (cdr state))))
            (apply-k saved-k val))))

      ;; ── k-top-wrap: bridge from meval-toplevel to meval ──
      ;; (k-top-wrap menv top-k)
      ;; val = result of evaluating the expression
      ;; top-k is a toplevel continuation (2-arg protocol)
      ((= tag 'k-top-wrap)
        (let ((menv  (nth 1 k))
              (top-k (nth 2 k)))
          (apply-k-top top-k val menv)))

      ;; Fallback
      (T val))))

;;; ── Toplevel Continuation Dispatch ──────────────────────────────────
;;; meval-toplevel uses a 2-arg protocol: (val, env) to thread defun bindings.

(defun apply-k-top (k val env)
  "Apply a toplevel continuation (receives value and environment)."
  (let ((tag (car k)))
    (cond
      ;; ── k-top-id: toplevel identity, just return val ──
      ((= tag 'k-top-id)
        val)

      ;; ── k-program-step: continue with remaining top-level forms ──
      ;; (k-program-step rest-exprs final-k)
      ((= tag 'k-program-step)
        (let ((rest    (nth 1 k))
              (final-k (nth 2 k)))
          (if (null rest)
            (apply-k final-k val)
            (meval-program rest env final-k))))

      ;; Fallback
      (T val))))

;;; ── The CPS Evaluator ───────────────────────────────────────────────
;;; No lambdas. Every continuation argument is a tagged list.

(defun meval (expr menv k)
  "Evaluate expr in menv, passing result to continuation k."
  (cond
    ;; Self-evaluating: NIL, T, numbers < 100
    ((null expr)        (apply-k k NIL))
    ((= expr T)         (apply-k k T))
    ((self-eval? expr)  (apply-k k expr))

    ;; Symbol lookup
    ((symbol? expr)     (apply-k k (m-lookup expr menv)))

    ;; Compound expression
    ((compound? expr)
      (let ((head (car expr)))
        (cond
          ;; (quote datum)
          ((= head 'quote)
            (apply-k k (car (cdr expr))))

          ;; (if test then else)
          ((= head 'if)
            (let ((then-branch (car (cdr (cdr expr))))
                  (else-part   (cdr (cdr (cdr expr)))))
              (let ((else-branch (if (null else-part) NIL (car else-part))))
                (meval (car (cdr expr)) menv
                  (list 'k-if then-branch else-branch menv k)))))

          ;; (cond (test val) ...)
          ((= head 'cond)
            (eval-cond (cdr expr) menv k))

          ;; (lambda (params) body)
          ((= head 'lambda)
            (apply-k k (make-closure NIL (car (cdr expr)) (car (cdr (cdr expr))) menv)))

          ;; (let ((x v) ...) body)
          ((= head 'let)
            (eval-let-bindings (car (cdr expr)) menv
              (list 'k-let-body (car (cdr (cdr expr))) k)))

          ;; (progn expr ...)
          ((= head 'progn)
            (eval-sequence (cdr expr) menv k))

          ;; ── REIFY ──────────────────────────────────────────
          ;; The 3-Lisp move: capture the current continuation and
          ;; environment as a first-class value.
          ;;
          ;; Returns: (reified-state <continuation> <environment> <expression>)
          ;; The continuation is a TAGGED DATA STRUCTURE — fully inspectable.
          ;; Use (car k) to see the type, (cdr k) to see captured values.
          ;; Use (k-walk k) to see the entire pending computation chain.
          ((= head 'reify)
            (apply-k k (list 'reified-state k menv expr)))

          ;; ── REFLECT ────────────────────────────────────────
          ;; Install a (possibly modified) state. Abandons the current
          ;; continuation and jumps to the one in the reified state.
          ;; (reflect state value) — eval state, eval value, jump.
          ((= head 'reflect)
            (meval (car (cdr expr)) menv
              (list 'k-reflect-state (car (cdr (cdr expr))) menv)))

          ;; Function application: (fn arg1 arg2 ...)
          (T
            (meval head menv
              (list 'k-apply-fn (cdr expr) menv k))))))

    ;; Fallback
    (T (apply-k k expr))))

;;; ── CPS helpers ─────────────────────────────────────────────────────
;;; All continuation arguments are tagged lists, no lambdas.

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
      (apply-k k (apply-builtin (builtin-name fn) args)))
    (T (apply-k k NIL))))

(defun eval-args (exprs menv k)
  "Evaluate argument list left-to-right, pass results to k."
  (if (null exprs) (apply-k k NIL)
    (meval (car exprs) menv
      (list 'k-args-head (cdr exprs) menv k))))

(defun eval-cond (clauses menv k)
  "Evaluate cond clauses in order."
  (if (null clauses) (apply-k k NIL)
    (meval (car (car clauses)) menv
      (list 'k-cond (cdr clauses) (car (cdr (car clauses))) menv k))))

(defun eval-let-bindings (bindings menv k)
  "Evaluate let bindings, extending env, then call k with new env."
  (if (null bindings) (apply-k k menv)
    (meval (car (cdr (car bindings))) menv
      (list 'k-let-bind (car (car bindings)) (cdr bindings) menv k))))

(defun eval-sequence (exprs menv k)
  "Evaluate a sequence, return last result."
  (if (null (cdr exprs))
    (meval (car exprs) menv k)
    (meval (car exprs) menv
      (list 'k-seq (cdr exprs) menv k))))

;;; ── Top-level program evaluation (handles defun) ────────────────────

(defun defun-form? (expr)
  (if (compound? expr) (= (car expr) 'defun) NIL))

(defun meval-toplevel (expr menv k)
  "Evaluate top-level form. k is a toplevel continuation (2-arg protocol)."
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
              (apply-k-top k rec-closure final-env))))))
    ;; Regular expression — bridge to standard continuation protocol
    (meval expr menv (list 'k-top-wrap menv k))))

(defun meval-program (exprs menv k)
  "Evaluate a list of top-level forms, threading env through defuns."
  (if (null exprs) (apply-k k NIL)
    (meval-toplevel (car exprs) menv
      (list 'k-program-step (cdr exprs) k))))

;;; ── Continuation Inspection Utilities ───────────────────────────────
;;; These let reified programs examine their own control flow.

(defun k-next (k)
  "Get the next continuation in the chain (or NIL if terminal)."
  (let ((tag (car k)))
    (cond
      ;; Terminal: no next continuation
      ((= tag 'k-id)             NIL)
      ((= tag 'k-reflect-state)  NIL)
      ((= tag 'k-reflect-jump)   NIL)
      ((= tag 'k-top-id)         NIL)
      ;; 2 fields: (tag f1 next-k) → position 2
      ((= tag 'k-let-body)       (nth 2 k))
      ((= tag 'k-do-apply)       (nth 2 k))
      ((= tag 'k-args-tail)      (nth 2 k))
      ;; 3 fields: (tag f1 f2 next-k) → position 3
      ((= tag 'k-seq)            (nth 3 k))
      ((= tag 'k-apply-fn)       (nth 3 k))
      ((= tag 'k-args-head)      (nth 3 k))
      ;; 4 fields: (tag f1 f2 f3 next-k) → position 4
      ((= tag 'k-if)             (nth 4 k))
      ((= tag 'k-cond)           (nth 4 k))
      ((= tag 'k-let-bind)       (nth 4 k))
      ;; Toplevel bridge: top-k is at position 2 (different protocol)
      ((= tag 'k-top-wrap)       (nth 2 k))
      ((= tag 'k-program-step)   (nth 2 k))
      ;; Unknown
      (T NIL))))

(defun k-depth (k)
  "Count the number of frames in a continuation chain."
  (if (null k) 0
    (if (= (car k) 'k-id) 1
      (+ 1 (k-depth (k-next k))))))

(defun k-walk (k)
  "Return list of all continuation tags in the chain."
  (if (null k) NIL
    (if (= (car k) 'k-id) (list 'k-id)
      (cons (car k) (k-walk (k-next k))))))

(defun describe-continuation (k)
  "Return a human-readable description of what k will do next."
  (if (null k) (list 'empty)
    (let ((tag (car k)))
      (cond
        ((= tag 'k-id)
          (list 'identity 'return-value))
        ((= tag 'k-if)
          (list 'if-branch 'then (nth 1 k) 'else (nth 2 k)))
        ((= tag 'k-cond)
          (list 'cond-clause 'consequent (nth 2 k)))
        ((= tag 'k-let-body)
          (list 'let-body 'expr (nth 1 k)))
        ((= tag 'k-let-bind)
          (list 'let-bind 'var (nth 1 k)))
        ((= tag 'k-seq)
          (list 'sequence 'remaining (nth 1 k)))
        ((= tag 'k-apply-fn)
          (list 'apply 'evaluating-args (nth 1 k)))
        ((= tag 'k-do-apply)
          (list 'apply 'calling-fn (nth 1 k)))
        ((= tag 'k-args-head)
          (list 'eval-args 'remaining (nth 1 k)))
        ((= tag 'k-args-tail)
          (list 'eval-args 'consing-head (nth 1 k)))
        ((= tag 'k-reflect-state)
          (list 'reflect 'evaluating-value (nth 1 k)))
        ((= tag 'k-reflect-jump)
          (list 'reflect 'jumping-to-saved-state))
        ((= tag 'k-top-wrap)
          (list 'toplevel 'returning))
        ((= tag 'k-program-step)
          (list 'program 'remaining-forms (nth 1 k)))
        (T (list 'unknown tag))))))

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
    (cons 'not (make-builtin 'not))
    (cons 'nth (make-builtin 'nth))))

;; Convenience: count entries in an alist
(defun m-length (lst)
  (if (null lst) 0 (+ 1 (m-length (cdr lst)))))
