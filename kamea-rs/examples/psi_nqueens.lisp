; psi_nqueens.lisp — N-Queens solver
;
; Counts the number of solutions to the N-Queens problem.
; Uses pure list-based backtracking search.
;
; Note: Ψ-Lisp uses saturating subtraction (- a b) = max(0, a-b).
; The algorithm avoids negative numbers by tracking distance upward.

(defun abs-diff (a b)
  (if (> a b) (- a b) (- b a)))

(defun safe? (queen dist placed)
  "Check if placing queen at column 'queen' conflicts with any placed queen.
   dist starts at 1 and counts up through the placed list."
  (if (null placed) T
    (let ((q (car placed)))
      (if (= queen q) NIL                           ; same column
        (if (= (abs-diff queen q) dist) NIL          ; same diagonal
          (safe? queen (+ dist 1) (cdr placed)))))))

(defun nqueens-count (n row placed)
  "Count solutions by trying each column in the current row."
  (if (= row n)
    1   ; all queens placed — one solution found
    (count-cols n 0 row placed)))

(defun count-cols (n col row placed)
  "Try placing a queen in each column of the current row."
  (if (= col n)
    0   ; tried all columns
    (+ (if (safe? col 1 placed)
         (nqueens-count n (+ row 1) (cons col placed))
         0)
       (count-cols n (+ col 1) row placed))))

(defun nqueens (n)
  (nqueens-count n 0 NIL))

; Run benchmarks
(print (nqueens 1))   ; 1
(print (nqueens 4))   ; 2
(print (nqueens 5))   ; 10
(print (nqueens 6))   ; 4
(print (nqueens 7))   ; 40
(print (nqueens 8))   ; 92
