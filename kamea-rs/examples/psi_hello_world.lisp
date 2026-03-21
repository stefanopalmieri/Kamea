; psi_hello_world.lisp — "Hello, world!\n" via Ψ-Lisp
;
; Port of hello_world.ds from the legacy Delta/Kamea IO atoms
; (IO_PUT, IO_SEQ with manual nibble encoding) to the Ψ∗ framework.
;
; In Ψ∗, IO is a machine-level concern — the algebra provides the
; instruction set (Q/E for data, g/f/η for pairs, ρ for branching),
; and the machine provides IO via builtins.
;
; Each character is a Q-chain integer (its ASCII code).
; Strings are lists of integers, terminated at NIL (⊥).
;
; Run with:  python3 psi_lisp.py examples/psi_hello_world.lisp

; ── Method 1: write-string on a string literal ──────────────
; String literals evaluate to lists of Q-chain ASCII codes.
; "Hello, world!\n" → (72 101 108 108 111 44 32 119 111 114 108 100 33 10)
; write-string walks the list, emitting each character.

(write-string "Hello, world!\n")

; ── Method 2: character-by-character with write-char ─────────
; Each integer is a Q-chain: 0 = App(Q,⊤), 72 = 73 Q-layers around ⊤.
; write-char decodes the integer and emits the character.
; This is the direct analogue of the legacy IO_PUT approach,
; but without manual nibble splitting.

(defun emit-hello ()
  (write-char 72)   ; H
  (write-char 101)  ; e
  (write-char 108)  ; l
  (write-char 108)  ; l
  (write-char 111)  ; o
  (write-char 44)   ; ,
  (write-char 32)   ; (space)
  (write-char 119)  ; w
  (write-char 111)  ; o
  (write-char 114)  ; r
  (write-char 108)  ; l
  (write-char 100)  ; d
  (write-char 33)   ; !
  (write-char 10))  ; \n

(emit-hello)

; ── Method 3: recursive list walker (pure Ψ∗) ───────────────
; Demonstrates that Ψ-Lisp's recursion + list operations
; (all backed by Ψ∗ primitives g/f/η) compose with IO.

(defun emit-chars (chars)
  (if (null chars)
    T
    (progn
      (write-char (car chars))
      (emit-chars (cdr chars)))))

(emit-chars '(72 101 108 108 111 44 32 119 111 114 108 100 33 10))
