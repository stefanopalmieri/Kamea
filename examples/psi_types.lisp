; psi_types.lisp — type distinction tests
; T (⊤), NIL (⊥), and integers (Q-chains rooted at ⊤) are all distinct.

;; null tests
(null NIL)              ; → T   (NIL is null)
(null 0)                ; → NIL (0 is not null)
(null T)                ; → NIL (T is not null)

;; zerop tests
(zerop 0)               ; → T   (0 IS zero)
(zerop 1)               ; → NIL (1 is not zero)
(zerop NIL)             ; → NIL (NIL is not zero)

;; if semantics — only NIL is falsy
(if NIL 'yes 'no)       ; → no  (NIL is falsy)
(if T 'yes 'no)         ; → yes (T is truthy)
(if 0 'yes 'no)         ; → yes (0 is truthy)
(if 1 'yes 'no)         ; → yes (1 is truthy)

;; Arithmetic
(+ 3 4)                 ; → 7
(- 5 2)                 ; → 3
(* 4 5)                 ; → 20

;; Lists terminate at NIL = ⊥
(defun add1 (x) (+ x 1))
(defun length (lst)
  (if (null lst) 0
      (+ 1 (length (cdr lst)))))
(defun mapcar (f lst)
  (if (null lst) NIL
      (cons (f (car lst)) (mapcar f (cdr lst)))))

(length (list 1 2 3))   ; → 3
(car (list 1 2 3))      ; → 1
(mapcar add1 (list 1 2 3)) ; → (2 3 4)

;; Fibonacci
(defun fib (n)
  (if (< n 2) n
      (+ (fib (- n 1)) (fib (- n 2)))))
(fib 8)                 ; → 21

;; Display distinguishes types
NIL                     ; → NIL
T                       ; → T
0                       ; → 0
1                       ; → 1
(list 1 2 3)            ; → (1 2 3)
(null (cdr (list 1)))   ; → T (cdr of singleton is NIL)

;; numberp predicate
(numberp 0)             ; → T
(numberp 42)            ; → T
(numberp NIL)           ; → NIL
(numberp T)             ; → NIL
