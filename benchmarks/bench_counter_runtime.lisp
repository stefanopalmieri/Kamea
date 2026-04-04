;;; bench_counter_runtime.lisp — SBCL counter arithmetic with argv inputs
;;; Run: sbcl --script benchmarks/bench_counter_runtime.lisp 8 30 10 2 10 100 75

(declaim (optimize (speed 3) (safety 0) (debug 0)))

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

;; Parse argv
(defvar *args* (mapcar #'parse-integer
                       (cdr sb-ext:*posix-argv*)))

(defun get-arg (i) (nth i *args*))

(defun counter-arith ()
  (+ (fib (get-arg 0))
     (fib-iter (get-arg 1))
     (fact (get-arg 2))
     (my-power (get-arg 3) (get-arg 4))
     (my-gcd (get-arg 5) (get-arg 6))))

;; Warmup
(counter-arith)

;; Bench
(let* ((iters 1000000)
       (start (get-internal-real-time))
       (result 0))
  (declare (fixnum result))
  (dotimes (i iters)
    (setf result (counter-arith)))
  (let* ((end (get-internal-real-time))
         (elapsed-sec (/ (- end start) (float internal-time-units-per-second)))
         (per-iter-us (* (/ elapsed-sec iters) 1e6)))
    (format t "Counter arithmetic: ~,3f µs/iter (~d iters, result=~d)~%"
            per-iter-us iters result)))
