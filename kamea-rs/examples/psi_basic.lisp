; psi_basic.lisp — atoms and lists

; Atoms
42
0
T
NIL

; Quoted data
(quote hello)
(quote (1 2 3))

; List construction
(cons 1 (cons 2 (cons 3 NIL)))

; car and cdr
(car (cons 10 (cons 20 NIL)))
(cdr (cons 10 (cons 20 NIL)))

; Nested pairs
(cons (cons 1 2) (cons 3 4))

; The list function
(list 1 2 3 4 5)
