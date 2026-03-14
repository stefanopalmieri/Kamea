// Ψ∗ Debugger — vanilla JS, computation in Web Worker

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

    hello: `; Hello World via Ψ\\u2217 Mini-Lisp
(write-string "Hello, world!\\n")

(defun emit-chars (chars)
  (if (null chars) T
      (progn
        (write-char (car chars))
        (emit-chars (cdr chars)))))
(emit-chars '(72 101 108 108 111 44 32 119 111 114 108 100 33 10))`
};

// ── Worker communication ──

const worker = new Worker('worker.js', { type: 'module' });
let nextId = 0;
const pending = new Map();
let workerReady = false;

worker.onmessage = (e) => {
    const { type, id, ...data } = e.data;
    if (type === 'ready') {
        workerReady = true;
        document.getElementById('stats').textContent = 'WASM loaded — ready';
        setRunning(false);
        return;
    }
    const cb = pending.get(id);
    if (cb) { pending.delete(id); cb(data); }
};

worker.onerror = (e) => {
    document.getElementById('stats').textContent = 'Worker error: ' + e.message;
};

function send(type, payload) {
    return new Promise((resolve) => {
        const id = nextId++;
        pending.set(id, resolve);
        worker.postMessage({ type, id, payload });
    });
}

// ── UI state ──

let running = false;
let selectedNode = null;
let lastResults = null;

function setRunning(v) {
    running = v;
    const btn = document.getElementById('btn-run');
    btn.disabled = v;
    btn.textContent = v ? '\u23f3 Running...' : '\u25b6 Run';
}

// ── Term tree rendering ──

const ATOM_CLASSES = {
    '\u22a4': 'tn-atom-top',    // ⊤
    '\u22a5': 'tn-atom-bot',    // ⊥
    '\u03c4': 'tn-atom-tau',    // τ
    'f': 'tn-atom-enc',
    'g': 'tn-atom-inert',
    'Q': 'tn-atom-op',
    'E': 'tn-atom-op',
    '\u03c1': 'tn-atom-op',     // ρ
    '\u03b7': 'tn-atom-op',     // η
    'Y': 'tn-atom-op',
};

function atomClass(name) {
    return ATOM_CLASSES[name] || 'tn-atom';
}

function renderTree(node, depth) {
    if (!node) return document.createTextNode('nil');
    depth = depth || 0;

    const el = document.createElement('div');
    el.className = 'tn';

    switch (node.kind) {
        case 'atom': {
            const lbl = document.createElement('span');
            lbl.className = 'tn-label ' + atomClass(node.value);
            lbl.textContent = node.value;
            lbl.addEventListener('click', () => selectNode(lbl, node));
            const arrow = document.createElement('span');
            arrow.className = 'tn-arrow leaf';
            arrow.textContent = '\u25b6';
            el.appendChild(arrow);
            el.appendChild(lbl);
            break;
        }
        case 'int': {
            const lbl = document.createElement('span');
            lbl.className = 'tn-label tn-int';
            lbl.textContent = node.value;
            lbl.title = 'Integer: ' + node.int_value + ' Q-layers around \u22a4';
            lbl.addEventListener('click', () => selectNode(lbl, node));
            const arrow = document.createElement('span');
            arrow.className = 'tn-arrow leaf';
            arrow.textContent = '\u25b6';
            el.appendChild(arrow);
            el.appendChild(lbl);
            break;
        }
        case 'list': {
            const toggle = document.createElement('button');
            toggle.className = 'tn-toggle';
            const arrow = document.createElement('span');
            arrow.className = 'tn-arrow open';
            arrow.textContent = '\u25b6';
            const lbl = document.createElement('span');
            lbl.className = 'tn-label tn-pair';
            lbl.textContent = 'list [' + node.list_items.length + ']';
            lbl.addEventListener('click', (e) => { e.stopPropagation(); selectNode(lbl, node); });
            toggle.appendChild(arrow);
            toggle.appendChild(lbl);
            el.appendChild(toggle);

            const children = document.createElement('div');
            children.className = 'tn-children';
            node.list_items.forEach((item, i) => {
                const wrapper = document.createElement('div');
                const idx = document.createElement('span');
                idx.className = 'tn-keyword';
                idx.textContent = i + ': ';
                wrapper.appendChild(idx);
                wrapper.appendChild(renderTree(item, depth + 1));
                children.appendChild(wrapper);
            });
            el.appendChild(children);

            toggle.addEventListener('click', () => {
                const open = !children.classList.contains('collapsed');
                children.classList.toggle('collapsed', open);
                arrow.classList.toggle('open', !open);
            });
            // Auto-collapse deep lists
            if (depth > 2 && node.list_items.length > 3) {
                children.classList.add('collapsed');
                arrow.classList.remove('open');
            }
            break;
        }
        case 'pair': {
            const toggle = document.createElement('button');
            toggle.className = 'tn-toggle';
            const arrow = document.createElement('span');
            arrow.className = 'tn-arrow open';
            arrow.textContent = '\u25b6';
            const lbl = document.createElement('span');
            lbl.className = 'tn-label tn-pair';
            lbl.textContent = 'pair';
            lbl.addEventListener('click', (e) => { e.stopPropagation(); selectNode(lbl, node); });
            toggle.appendChild(arrow);
            toggle.appendChild(lbl);
            el.appendChild(toggle);

            const children = document.createElement('div');
            children.className = 'tn-children';
            const carWrap = document.createElement('div');
            const carLbl = document.createElement('span');
            carLbl.className = 'tn-keyword';
            carLbl.textContent = 'car: ';
            carWrap.appendChild(carLbl);
            carWrap.appendChild(renderTree(node.children[0], depth + 1));
            children.appendChild(carWrap);

            const cdrWrap = document.createElement('div');
            const cdrLbl = document.createElement('span');
            cdrLbl.className = 'tn-keyword';
            cdrLbl.textContent = 'cdr: ';
            cdrWrap.appendChild(cdrLbl);
            cdrWrap.appendChild(renderTree(node.children[1], depth + 1));
            children.appendChild(cdrWrap);
            el.appendChild(children);

            toggle.addEventListener('click', () => {
                const open = !children.classList.contains('collapsed');
                children.classList.toggle('collapsed', open);
                arrow.classList.toggle('open', !open);
            });
            break;
        }
        case 'app': {
            const toggle = document.createElement('button');
            toggle.className = 'tn-toggle';
            const arrow = document.createElement('span');
            arrow.className = 'tn-arrow open';
            arrow.textContent = '\u25b6';
            const lbl = document.createElement('span');
            lbl.className = 'tn-label tn-app';
            lbl.textContent = 'app';
            lbl.addEventListener('click', (e) => { e.stopPropagation(); selectNode(lbl, node); });
            toggle.appendChild(arrow);
            toggle.appendChild(lbl);
            el.appendChild(toggle);

            const children = document.createElement('div');
            children.className = 'tn-children';
            const funWrap = document.createElement('div');
            const funLbl = document.createElement('span');
            funLbl.className = 'tn-keyword';
            funLbl.textContent = 'fun: ';
            funWrap.appendChild(funLbl);
            funWrap.appendChild(renderTree(node.children[0], depth + 1));
            children.appendChild(funWrap);

            const argWrap = document.createElement('div');
            const argLbl = document.createElement('span');
            argLbl.className = 'tn-keyword';
            argLbl.textContent = 'arg: ';
            argWrap.appendChild(argLbl);
            argWrap.appendChild(renderTree(node.children[1], depth + 1));
            children.appendChild(argWrap);
            el.appendChild(children);

            toggle.addEventListener('click', () => {
                const open = !children.classList.contains('collapsed');
                children.classList.toggle('collapsed', open);
                arrow.classList.toggle('open', !open);
            });
            // Auto-collapse deep apps
            if (depth > 3) {
                children.classList.add('collapsed');
                arrow.classList.remove('open');
            }
            break;
        }
        default: {
            el.textContent = node.value || '...';
        }
    }
    return el;
}

function selectNode(labelEl, node) {
    if (selectedNode) selectedNode.classList.remove('selected');
    labelEl.classList.add('selected');
    selectedNode = labelEl;
}

function showTree(tree, label) {
    const container = document.getElementById('term-tree');
    const labelEl = document.getElementById('tree-label');
    container.innerHTML = '';
    labelEl.textContent = label || '';
    if (tree) {
        container.appendChild(renderTree(tree, 0));
    }
}

function showResultTrees(results) {
    const container = document.getElementById('term-tree');
    const labelEl = document.getElementById('tree-label');
    container.innerHTML = '';

    if (!results || results.length === 0) {
        labelEl.textContent = '';
        return;
    }

    labelEl.textContent = results.length + ' result' + (results.length === 1 ? '' : 's');

    results.forEach((r, i) => {
        const wrapper = document.createElement('div');
        wrapper.style.marginBottom = '8px';

        const header = document.createElement('div');
        header.style.cursor = 'pointer';
        header.style.padding = '4px 8px';
        header.style.borderRadius = '4px';
        header.style.background = 'rgba(255,255,255,0.03)';
        header.style.marginBottom = '4px';
        header.style.fontSize = '12px';
        header.style.color = '#4ecca3';
        header.textContent = '\u25b6 ' + r.display;

        const treeEl = document.createElement('div');
        treeEl.style.display = 'none';
        treeEl.style.marginLeft = '8px';
        treeEl.appendChild(renderTree(r.tree, 0));

        header.addEventListener('click', () => {
            const open = treeEl.style.display !== 'none';
            treeEl.style.display = open ? 'none' : 'block';
            header.textContent = (open ? '\u25b6 ' : '\u25bc ') + r.display;
        });

        wrapper.appendChild(header);
        wrapper.appendChild(treeEl);
        container.appendChild(wrapper);
    });
}

// ── Cayley table modal ──

let tableBuilt = false;

async function buildCayleyTable() {
    if (tableBuilt) return;
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
            td.textContent = data.names[data.cells[i][j]];
            td.title = data.names[i] + ' \u00b7 ' + data.names[j] + ' = ' + data.names[data.cells[i][j]];
            row.appendChild(td);
        }
        tbody.appendChild(row);
    }
    tbl.appendChild(tbody);
    container.innerHTML = '';
    container.appendChild(tbl);
    tableBuilt = true;
}

function toggleTableModal() {
    const modal = document.getElementById('table-modal');
    const isHidden = modal.classList.contains('hidden');
    if (isHidden) {
        buildCayleyTable();
        modal.classList.remove('hidden');
    } else {
        modal.classList.add('hidden');
    }
}

// ── Run / Reset ──

async function runProgram() {
    if (!workerReady || running) return;
    const source = document.getElementById('source').value;
    const output = document.getElementById('output');

    setRunning(true);
    output.textContent = '';
    showResultTrees([]);
    document.getElementById('stats').textContent = 'Running...';

    const start = performance.now();
    const data = await send('run', { source });
    const elapsed = performance.now() - start;

    if (data.error) {
        output.textContent = 'Error: ' + data.error;
        setRunning(false);
        return;
    }

    const result = JSON.parse(data.result);

    if (result.error) {
        output.textContent = 'Error: ' + result.error;
    } else {
        let text = result.results.map(r => r.display).join('\n');
        if (result.io_output) text = result.io_output + (text ? '\n' + text : '');
        output.textContent = text;
        lastResults = result.results;
        showResultTrees(result.results);
    }

    const stats = JSON.parse(data.stats);
    document.getElementById('stats').textContent =
        'Done \u2014 arena=' + stats.arena_size + ' nodes, time=' + elapsed.toFixed(1) + 'ms';
    setRunning(false);
}

async function resetMachine() {
    if (!workerReady) return;
    await send('reset');
    document.getElementById('output').textContent = '';
    showResultTrees([]);
    lastResults = null;
    document.getElementById('stats').textContent = 'Reset \u2014 ready';
}

function loadExample(name) {
    if (name && EXAMPLES[name]) {
        document.getElementById('source').value = EXAMPLES[name];
    }
}

// ── Event listeners ──

document.getElementById('btn-run').addEventListener('click', runProgram);
document.getElementById('btn-reset').addEventListener('click', resetMachine);
document.getElementById('btn-table').addEventListener('click', toggleTableModal);

document.getElementById('examples').addEventListener('change', (e) => {
    loadExample(e.target.value);
    e.target.value = '';
});

document.getElementById('source').addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        e.preventDefault();
        runProgram();
    }
    // Tab inserts two spaces
    if (e.key === 'Tab') {
        e.preventDefault();
        const ta = e.target;
        const start = ta.selectionStart;
        ta.value = ta.value.substring(0, start) + '  ' + ta.value.substring(ta.selectionEnd);
        ta.selectionStart = ta.selectionEnd = start + 2;
    }
});

// Modal close
document.querySelector('.modal-close').addEventListener('click', toggleTableModal);
document.querySelector('.modal-backdrop').addEventListener('click', toggleTableModal);
document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') {
        const modal = document.getElementById('table-modal');
        if (!modal.classList.contains('hidden')) toggleTableModal();
    }
});

// ── Init ──

document.getElementById('stats').textContent = 'Loading WASM...';
worker.postMessage({ type: 'init', id: -1 });
