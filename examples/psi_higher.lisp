; psi_higher.lisp — higher-order functions

(defun add1 (x) (+ x 1))

; Map
(defun mapcar (f lst)
  (if (null lst)
      NIL
      (cons (f (car lst))
            (mapcar f (cdr lst)))))

(mapcar add1 (list 1 2 3))
(mapcar (lambda (x) (* x x)) (list 1 2 3 4 5))

; Filter (remove-if-not)
(defun remove-if-not (pred lst)
  (if (null lst)
      NIL
      (if (pred (car lst))
          (cons (car lst) (remove-if-not pred (cdr lst)))
          (remove-if-not pred (cdr lst)))))

(defun evenp (n) (= (mod n 2) 0))
(remove-if-not evenp (list 1 2 3 4 5 6 7 8 9 10))

; Reduce (fold left)
(defun reduce (f acc lst)
  (if (null lst)
      acc
      (reduce f (f acc (car lst)) (cdr lst))))

(reduce + 0 (list 1 2 3 4 5))
(reduce * 1 (list 1 2 3 4 5))

; Length via reduce
(defun length (lst)
  (reduce (lambda (acc x) (+ acc 1)) 0 lst))

(length (list 1 2 3))
(length NIL)

; Append
(defun append (a b)
  (if (null a)
      b
      (cons (car a) (append (cdr a) b))))

(append (list 1 2 3) (list 4 5 6))

; Reverse via reduce
(defun reverse (lst)
  (reduce (lambda (acc x) (cons x acc)) NIL lst))

(reverse (list 1 2 3 4 5))
