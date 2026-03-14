; psi_fibonacci.lisp — Fibonacci sequence

(defun fib (n)
  (if (< n 2)
      n
      (+ (fib (- n 1))
         (fib (- n 2)))))

(fib 0)
(fib 1)
(fib 2)
(fib 3)
(fib 5)
(fib 8)
(fib 10)

; Iterative fibonacci (much faster for large n)
(defun fib-iter (n)
  (defun helper (a b count)
    (if (= count 0)
        a
        (helper b (+ a b) (- count 1))))
  (helper 0 1 n))

(fib-iter 10)
(fib-iter 20)
(fib-iter 30)

; Reverse (needed for fib-list)
(defun reverse (lst)
  (defun rev-helper (l acc)
    (if (null l) acc
        (rev-helper (cdr l) (cons (car l) acc))))
  (rev-helper lst NIL))

; First 10 Fibonacci numbers
(defun fib-list (n)
  (defun fl-helper (i acc)
    (if (= i n)
        (reverse acc)
        (fl-helper (+ i 1) (cons (fib-iter i) acc))))
  (fl-helper 0 NIL))

(fib-list 10)
