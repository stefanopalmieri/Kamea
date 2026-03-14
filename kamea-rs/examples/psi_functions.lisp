; psi_functions.lisp — lambda and application

; Simple function
(defun square (x) (* x x))
(square 5)
(square 12)

; Multi-argument function
(defun add3 (a b c) (+ a (+ b c)))
(add3 1 2 3)

; Lambda
((lambda (x) (+ x 1)) 10)

; Let binding
(let ((x 5) (y 3))
  (+ x y))

; Function as value
(setq double (lambda (x) (* x 2)))
(double 7)

; Composition via lambda
(defun compose (f g)
  (lambda (x) (f (g x))))

(setq add1 (lambda (x) (+ x 1)))
(setq double-then-add1 (compose add1 double))
(double-then-add1 5)
