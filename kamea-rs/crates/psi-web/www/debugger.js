// Ψ∗ Debugger — vanilla JS, computation runs in a Web Worker

const EXAMPLES = {
    basic: `; Atoms and lists
42
0
T
NIL

; Quoted data
(quote hello)
(quote (1 2 3))

; List construction
(cons 1 (cons 2 (cons 3 NIL)))
(car (cons 10 (cons 20 NIL)))
(cdr (cons 10 (cons 20 NIL)))
(list 1 2 3 4 5)`,

    arithmetic: `; Counter operations via Q/E
(+ 3 4)
(- 10 3)
(* 4 5)
(zerop 0)
(zerop 5)
(< 3 5)
(> 3 5)
(= 7 7)
(+ (* 3 4) (* 5 6))
(mod 17 5)`,

    functions: `; Lambda and application
(defun square (x) (* x x))
(square 5)
(square 12)

(defun add3 (a b c) (+ a (+ b c)))
(add3 1 2 3)

((lambda (x) (+ x 1)) 10)

(let ((x 5) (y 3)) (+ x y))

(setq double (lambda (x) (* x 2)))
(double 7)

(defun compose (f g)
  (lambda (x) (f (g x))))
(setq add1 (lambda (x) (+ x 1)))
(setq double-then-add1 (compose add1 double))
(double-then-add1 5)`,

    recursion: `; Recursive functions
(defun fact (n)
  (if (= n 0) 1
      (* n (fact (- n 1)))))
(fact 0)
(fact 1)
(fact 5)
(fact 10)

(defun sum-to (n)
  (if (= n 0) 0
      (+ n (sum-to (- n 1)))))
(sum-to 10)
(sum-to 100)

(defun power (base exp)
  (if (= exp 0) 1
      (* base (power base (- exp 1)))))
(power 2 10)

(defun gcd (a b)
  (if (= b 0) a
      (gcd b (mod a b))))
(gcd 12 8)
(gcd 100 75)`,

    fibonacci: `; Fibonacci sequence
(defun fib (n)
  (if (< n 2) n
      (+ (fib (- n 1))
         (fib (- n 2)))))
(fib 0)
(fib 1)
(fib 5)
(fib 8)
(fib 10)

; Iterative (fast)
(defun fib-iter (n)
  (defun helper (a b count)
    (if (= count 0) a
        (helper b (+ a b) (- count 1))))
  (helper 0 1 n))
(fib-iter 10)
(fib-iter 20)
(fib-iter 30)`,

    higher: `; Higher-order functions
(defun add1 (x) (+ x 1))

(defun mapcar (f lst)
  (if (null lst) NIL
      (cons (f (car lst))
            (mapcar f (cdr lst)))))
(mapcar add1 (list 1 2 3))
(mapcar (lambda (x) (* x x)) (list 1 2 3 4 5))

(defun remove-if-not (pred lst)
  (if (null lst) NIL
      (if (pred (car lst))
          (cons (car lst) (remove-if-not pred (cdr lst)))
          (remove-if-not pred (cdr lst)))))
(defun evenp (n) (= (mod n 2) 0))
(remove-if-not evenp (list 1 2 3 4 5 6 7 8 9 10))

(defun reduce (f acc lst)
  (if (null lst) acc
      (reduce f (f acc (car lst)) (cdr lst))))
(reduce + 0 (list 1 2 3 4 5))
(reduce * 1 (list 1 2 3 4 5))`,

    types: `; Type distinction tests
(null NIL)
(null 0)
(null T)
(zerop 0)
(zerop 1)
(zerop NIL)

; Only NIL is falsy
(if NIL 'yes 'no)
(if T 'yes 'no)
(if 0 'yes 'no)
(if 1 'yes 'no)

; Arithmetic
(+ 3 4)
(- 5 2)
(* 4 5)

; Fibonacci
(defun fib (n)
  (if (< n 2) n
      (+ (fib (- n 1)) (fib (- n 2)))))
(fib 8)`,

    hello: `; Hello World via Ψ∗ Mini-Lisp
(write-string "Hello, world!\\n")

(defun emit-chars (chars)
  (if (null chars) T
      (progn
        (write-char (car chars))
        (emit-chars (cdr chars)))))
(emit-chars '(72 101 108 108 111 44 32 119 111 114 108 100 33 10))`
};

// --- Worker communication ---

const worker = new Worker('worker.js', { type: 'module' });
let nextId = 0;
const pending = new Map();
let workerReady = false;

worker.onmessage = (e) => {
    const { type, id, ...data } = e.data;

    if (type === 'ready') {
        workerReady = true;
        buildCayleyTable();
        document.getElementById('stats').textContent = 'WASM loaded — ready';
        setRunning(false);
        return;
    }

    const cb = pending.get(id);
    if (cb) {
        pending.delete(id);
        cb(data);
    }
};

worker.onerror = (e) => {
    console.error('Worker error:', e);
    document.getElementById('stats').textContent = 'Worker error: ' + e.message;
};

function send(type, payload) {
    return new Promise((resolve) => {
        const id = nextId++;
        pending.set(id, resolve);
        worker.postMessage({ type, id, payload });
    });
}

// --- UI state ---

let running = false;

function setRunning(v) {
    running = v;
    const btn = document.getElementById('btn-run');
    btn.disabled = v;
    btn.textContent = v ? '⏳ Running...' : '▶ Run';
}

// --- Cayley table (fetched from worker once) ---

async function buildCayleyTable() {
    const { table } = await send('table');
    const data = JSON.parse(table);
    const container = document.getElementById('cayley-container');

    const tbl = document.createElement('table');
    const thead = document.createElement('thead');
    const headerRow = document.createElement('tr');
    headerRow.appendChild(document.createElement('th'));
    for (let j = 0; j < data.size; j++) {
        const th = document.createElement('th');
        th.textContent = data.names[j];
        th.className = 'role-' + data.roles[j];
        headerRow.appendChild(th);
    }
    thead.appendChild(headerRow);
    tbl.appendChild(thead);

    const tbody = document.createElement('tbody');
    for (let i = 0; i < data.size; i++) {
        const row = document.createElement('tr');
        const th = document.createElement('th');
        th.textContent = data.names[i];
        th.className = 'role-' + data.roles[i];
        row.appendChild(th);

        for (let j = 0; j < data.size; j++) {
            const td = document.createElement('td');
            td.textContent = data.cells[i][j];
            td.id = `cell-${i}-${j}`;
            row.appendChild(td);
        }
        tbody.appendChild(row);
    }
    tbl.appendChild(tbody);
    container.innerHTML = '';
    container.appendChild(tbl);
}

// --- Run / Reset ---

async function runProgram() {
    if (!workerReady || running) return;
    const source = document.getElementById('source').value;
    const output = document.getElementById('output');

    setRunning(true);
    output.textContent = '';
    document.getElementById('stats').textContent = 'Running...';

    const start = performance.now();
    const data = await send('run', { source });
    const elapsed = performance.now() - start;

    if (data.error) {
        output.textContent = 'Error: ' + data.error;
    } else {
        output.textContent = data.result;
        const stats = JSON.parse(data.stats);
        document.getElementById('stats').textContent =
            `Done — arena=${stats.arena_size} nodes, time=${elapsed.toFixed(1)}ms`;
    }
    setRunning(false);
}

async function resetMachine() {
    if (!workerReady) return;
    await send('reset');
    document.getElementById('output').textContent = '';
    document.getElementById('stats').textContent = 'Reset — ready';
}

function loadExample(name) {
    if (name && EXAMPLES[name]) {
        document.getElementById('source').value = EXAMPLES[name];
    }
}

// --- Event listeners ---

document.getElementById('btn-run').addEventListener('click', runProgram);
document.getElementById('btn-reset').addEventListener('click', resetMachine);
document.getElementById('examples').addEventListener('change', (e) => {
    loadExample(e.target.value);
    e.target.value = '';
});

document.getElementById('source').addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        e.preventDefault();
        runProgram();
    }
});

// --- Init ---

document.getElementById('stats').textContent = 'Loading WASM...';
worker.postMessage({ type: 'init', id: -1 });
