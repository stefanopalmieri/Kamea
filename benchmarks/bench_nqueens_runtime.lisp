;;; bench_nqueens_runtime.lisp — SBCL N-Queens with argv input
;;; Run: sbcl --script benchmarks/bench_nqueens_runtime.lisp 8

(declaim (optimize (speed 3) (safety 0) (debug 0)))

(defun abs-diff (a b)
  (declare (fixnum a b))
  (if (> a b) (- a b) (- b a)))

(defun safe-p (queen dist placed)
  (declare (fixnum queen dist))
  (if (null placed) t
      (let ((q (car placed)))
        (declare (fixnum q))
        (cond ((= queen q) nil)
              ((= (abs-diff queen q) dist) nil)
              (t (safe-p queen (1+ dist) (cdr placed)))))))

(defun nqueens-count (n row placed)
  (declare (fixnum n row))
  (if (= row n) 1
      (count-cols n 0 row placed)))

(defun count-cols (n col row placed)
  (declare (fixnum n col row))
  (if (= col n) 0
      (the fixnum
           (+ (if (safe-p col 1 placed)
                  (nqueens-count n (1+ row) (cons col placed))
                  0)
              (count-cols n (1+ col) row placed)))))

(defun nqueens (n)
  (nqueens-count n 0 nil))

(defvar *n* (parse-integer (second sb-ext:*posix-argv*)))

;; Warmup
(nqueens *n*)

;; Bench
(let* ((iters 10000)
       (start (get-internal-real-time))
       (result 0))
  (declare (fixnum result))
  (dotimes (i iters)
    (setf result (nqueens *n*)))
  (let* ((end (get-internal-real-time))
         (elapsed-sec (/ (- end start) (float internal-time-units-per-second)))
         (per-iter-us (* (/ elapsed-sec iters) 1e6)))
    (format t "N-Queens(~d):        ~,1f µs/iter (~d iters, result=~d)~%"
            *n* per-iter-us iters result)))
