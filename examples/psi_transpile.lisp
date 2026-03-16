; ═══════════════════════════════════════════════════════════════════════
; Ψ∗ Transpiler — a Ψ-Lisp program that emits Rust code
; ═══════════════════════════════════════════════════════════════════════
;
; Self-hosted transpiler: a Ψ-Lisp program that takes tagged-pair
; expression trees (same encoding as psi_specialize.lisp) and emits
; valid Rust source code targeting psi_runtime.rs.
;
; This closes the Futamura projection 3 loop: the specializer can
; specialize THIS transpiler on a known program to produce a
; residual Rust-emitting program.
;
; Usage:
;   python3 psi_lisp.py --table=c examples/psi_transpile.lisp
;
; The output is a complete Rust program that can be compiled with:
;   rustc -O -o /tmp/out /tmp/out.rs
; ═══════════════════════════════════════════════════════════════════════

; ── Expression constructors (shared with psi_specialize.lisp) ────────

(defun mk-atom (n)       (cons 0 n))
(defun mk-var (name)     (cons 1 name))
(defun mk-dot (a b)      (cons 2 (cons a b)))
(defun mk-if (test th el)  (cons 3 (cons test (cons th el))))
(defun mk-let (x val body) (cons 4 (cons x (cons val body))))
(defun mk-lam (x body)   (cons 5 (cons x body)))
(defun mk-app (fn arg)   (cons 6 (cons fn arg)))

; ── Expression accessors ─────────────────────────────────────────────

(defun expr-tag (e)   (car e))
(defun expr-payload (e) (cdr e))

(defun dot-a (e) (car (cdr e)))
(defun dot-b (e) (cdr (cdr e)))

(defun if-test (e) (car (cdr e)))
(defun if-then (e) (car (cdr (cdr e))))
(defun if-else (e) (cdr (cdr (cdr e))))

(defun let-var (e)  (car (cdr e)))
(defun let-val (e)  (car (cdr (cdr e))))
(defun let-body (e) (cdr (cdr (cdr e))))

(defun lam-var (e)  (car (cdr e)))
(defun lam-body (e) (cdr (cdr e)))

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

; ═══════════════════════════════════════════════════════════════════════
; Emission helpers — output Rust code via write-char / write-string
; ═══════════════════════════════════════════════════════════════════════

(defun emit-newline ()
  (write-char 10))

; emit-int: write decimal digits for a non-negative integer
; Uses / (integer division) and mod for digit decomposition
(defun emit-int (n)
  (if (< n 10)
      (write-char (+ n 48))  ; 48 = ASCII '0'
      (begin
        (emit-int (/ n 10))
        (write-char (+ (mod n 10) 48)))))

; emit-varname: write "_vN" where N is the variable name (integer)
(defun emit-varname (name)
  (write-string "_v")
  (emit-int name))

; ═══════════════════════════════════════════════════════════════════════
; Core: transpile-expr — emits a Rust expression for a tagged-pair AST
; ═══════════════════════════════════════════════════════════════════════

(defun transpile-expr (e)
  (cond
    ; Atom(n) → "N_i64"
    ((is-atom e)
     (begin
       (emit-int (expr-payload e))
       (write-string "_i64")))

    ; Var(name) → "_vN"
    ((is-var e)
     (emit-varname (expr-payload e)))

    ; Dot(a, b) — with INC/INV/DEC specialization
    ((is-dot e)
     (let ((a (dot-a e))
           (b (dot-b e)))
       (if (and (is-atom a) (= (expr-payload a) 13))
           ; INC specialization
           (begin
             (write-string "psi_inc(")
             (transpile-expr b)
             (write-string " as u8) as PsiVal"))
           (if (and (is-atom a) (= (expr-payload a) 14))
               ; INV specialization
               (begin
                 (write-string "psi_inv(")
                 (transpile-expr b)
                 (write-string " as u8) as PsiVal"))
               (if (and (is-atom a) (= (expr-payload a) 15))
                   ; DEC specialization
                   (begin
                     (write-string "psi_dec(")
                     (transpile-expr b)
                     (write-string " as u8) as PsiVal"))
                   ; General case
                   (begin
                     (write-string "psi_dot(")
                     (transpile-expr a)
                     (write-string " as u8, ")
                     (transpile-expr b)
                     (write-string " as u8) as PsiVal")))))))

    ; If(test, then, else) → "if is_true(test) { then } else { else }"
    ((is-if e)
     (begin
       (write-string "if (")
       (transpile-expr (if-test e))
       (write-string ") != 1_i64 { ")
       (transpile-expr (if-then e))
       (write-string " } else { ")
       (transpile-expr (if-else e))
       (write-string " }")))

    ; Let(x, val, body) → "{ let _vX: PsiVal = val; body }"
    ((is-let e)
     (begin
       (write-string "{ let ")
       (emit-varname (let-var e))
       (write-string ": PsiVal = ")
       (transpile-expr (let-val e))
       (write-string "; ")
       (transpile-expr (let-body e))
       (write-string " }")))

    ; Lam — bare lambda (specializer should have eliminated these)
    ((is-lam e)
     (write-string "PSI_NIL /* bare lambda */"))

    ; App — bare application (specializer should have eliminated these)
    ((is-app e)
     (write-string "PSI_NIL /* bare app */"))

    ; Fallback
    (T (write-string "PSI_NIL /* unknown */"))))

; ═══════════════════════════════════════════════════════════════════════
; Entry point: transpile-main — emits a complete Rust program
; ═══════════════════════════════════════════════════════════════════════

(defun transpile-main (e)
  (write-string "// Generated by psi_transpile.lisp")
  (emit-newline)
  (write-string "#![allow(non_snake_case, unused_parens, unused_variables)]")
  (emit-newline)
  (write-string "#[path = ")
  (write-char 34)  ; "
  (write-string "psi_runtime.rs")
  (write-char 34)  ; "
  (write-string "]")
  (emit-newline)
  (write-string "mod psi_runtime;")
  (emit-newline)
  (write-string "use psi_runtime::*;")
  (emit-newline)
  (emit-newline)
  (write-string "fn main() {")
  (emit-newline)
  (write-string "    let arena = Arena::new();")
  (emit-newline)
  (write-string "    let _result: PsiVal = ")
  (transpile-expr e)
  (write-string ";")
  (emit-newline)
  (write-string "    psi_println(&arena, _result);")
  (emit-newline)
  (write-string "}")
  (emit-newline))
