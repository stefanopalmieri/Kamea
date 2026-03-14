; psi_recursion.lisp — recursive functions

; Factorial
(defun fact (n)
  (if (= n 0)
      1
      (* n (fact (- n 1)))))

(fact 0)
(fact 1)
(fact 5)
(fact 10)

; Sum from 1 to n
(defun sum-to (n)
  (if (= n 0)
      0
      (+ n (sum-to (- n 1)))))

(sum-to 10)
(sum-to 100)

; Power
(defun power (base exp)
  (if (= exp 0)
      1
      (* base (power base (- exp 1)))))

(power 2 10)
(power 3 5)

; GCD (Euclid)
(defun gcd (a b)
  (if (= b 0)
      a
      (gcd b (mod a b))))

(gcd 12 8)
(gcd 100 75)
