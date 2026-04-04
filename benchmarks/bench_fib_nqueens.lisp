;;; bench_fib_nqueens.lisp — SBCL benchmark matching Psi-Lisp fib + nqueens
;;; Run: sbcl --script benchmarks/bench_fib_nqueens.lisp

(declaim (optimize (speed 3) (safety 0) (debug 0)))

;;; --- Counter arithmetic (matching README: fib(8) + fib-iter(30) + fact(10) + power(2,10) + gcd(100,75)) ---

(defun fib (n)
  (declare (fixnum n))
  (if (< n 2) n
      (the fixnum (+ (fib (- n 1)) (fib (- n 2))))))

(defun fib-iter (n)
  (declare (fixnum n))
  (loop with a fixnum = 0
        with b fixnum = 1
        repeat n
        do (psetf a b b (+ a b))
        finally (return a)))

(defun fact (n)
  (declare (fixnum n))
  (if (= n 0) 1
      (the fixnum (* n (fact (- n 1))))))

(defun my-power (base exp)
  (declare (fixnum base exp))
  (if (= exp 0) 1
      (the fixnum (* base (my-power base (- exp 1))))))

(defun my-gcd (a b)
  (declare (fixnum a b))
  (if (= b 0) a
      (my-gcd b (mod a b))))

(defun counter-arith ()
  (+ (fib 8) (fib-iter 30) (fact 10) (my-power 2 10) (my-gcd 100 75)))

;;; --- N-Queens(8) ---

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

;;; --- Timing ---

(defun bench-counter (iters)
  (let ((start (get-internal-real-time))
        (result 0))
    (declare (fixnum result))
    (dotimes (i iters)
      (setf result (counter-arith)))
    (let* ((end (get-internal-real-time))
           (elapsed-sec (/ (- end start) (float internal-time-units-per-second)))
           (per-iter-us (* (/ elapsed-sec iters) 1e6)))
      (format t "Counter arithmetic: ~,3f µs/iter (~d iters, result=~d)~%"
              per-iter-us iters result))))

(defun bench-nqueens (iters)
  (let ((start (get-internal-real-time))
        (result 0))
    (declare (fixnum result))
    (dotimes (i iters)
      (setf result (nqueens 8)))
    (let* ((end (get-internal-real-time))
           (elapsed-sec (/ (- end start) (float internal-time-units-per-second)))
           (per-iter-us (* (/ elapsed-sec iters) 1e6)))
      (format t "N-Queens(8):        ~,1f µs/iter (~d iters, result=~d)~%"
              per-iter-us iters result))))

;; Warmup
(counter-arith)
(nqueens 8)

;; Bench
(bench-counter 1000000)
(bench-nqueens 10000)
