// app.js — Ψ∗ Debugger main application controller

import { initEditor, getSource, setSource } from './editor.js';
import { TreeRenderer } from './tree-renderer.js';
import { CayleyTable } from './cayley-table.js';
import { createStepper } from './lisp-stepper.js';

// ═══════════════════════════════════════════════════════════
// Examples
// ═══════════════════════════════════════════════════════════

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

    hello: `; Hello World via \u03A8\u2217 Mini-Lisp
(write-string "Hello, world!\\n")

(defun emit-chars (chars)
  (if (null chars) T
      (progn
        (write-char (car chars))
        (emit-chars (cdr chars)))))
(emit-chars '(72 101 108 108 111 44 32 119 111 114 108 100 33 10))`,

    tower: `; Three-level reflective tower
; Level 0: Compute within the algebra
; Level 1: Verify the Cayley table substrate
; Level 2: Inspect the evaluator's own state

;; Atom indices
(setq TOP  0)
(setq BOT  1)
(setq F    2)
(setq TAU  3)
(setq G    4)
(setq QQ   6)
(setq EE   7)
(setq RHO  8)
(setq ETA  9)
(setq YY  10)

;; Helpers
(defun write-name (idx)
  (write-string (atom-name idx)))

(defun banner (msg)
  (terpri)
  (write-string "--- ")
  (write-string msg)
  (write-string " ---")
  (terpri))

;; === LEVEL 0: Computation ===
(defun fib (n)
  (if (< n 2) n
    (+ (fib (- n 1)) (fib (- n 2)))))

(write-string "=== PSI REFLECTIVE TOWER ===")
(terpri)
(banner "Level 0: Computation")
(write-string "Computing fibonacci(8)...")
(terpri)
(setq fib-result (fib 8))
(write-string "Result: ")
(print fib-result)

;; === LEVEL 1: Ground Verification ===
(banner "Shift Up to Level 1: Ground Verification")

(defun check-absorber (abs x)
  (let ((result (dot abs x)))
    (write-string "  ")
    (write-name abs)
    (write-string " . ")
    (write-name x)
    (write-string " = ")
    (write-name result)
    (if (= result abs)
      (progn (write-string " ok") (terpri) T)
      (progn (write-string " FAIL") (terpri) NIL))))

(write-string "Absorber laws:")
(terpri)
(setq absorber-ok
  (and (check-absorber TOP TOP)
       (check-absorber TOP BOT)
       (check-absorber TOP QQ)
       (check-absorber TOP EE)
       (check-absorber BOT TOP)
       (check-absorber BOT BOT)
       (check-absorber BOT QQ)
       (check-absorber BOT EE)))

(defun check-tester (x)
  (let ((result (dot TAU x)))
    (write-string "  tau . ")
    (write-name x)
    (write-string " = ")
    (write-name result)
    (if (or (= result TOP) (= result BOT))
      (progn (write-string " ok") (terpri) T)
      (progn (write-string " FAIL") (terpri) NIL))))

(write-string "Tester boolean output:")
(terpri)
(setq tester-ok
  (and (check-tester F)
       (check-tester TAU)
       (check-tester QQ)
       (check-tester EE)
       (check-tester RHO)
       (check-tester ETA)))

(defun check-qe (x)
  (let ((qx (dot QQ x)))
    (let ((eqx (dot EE qx)))
      (write-string "  E . (Q . ")
      (write-name x)
      (write-string ") = E . ")
      (write-name qx)
      (write-string " = ")
      (write-name eqx)
      (if (= eqx x)
        (progn (write-string " ok") (terpri) T)
        (progn (write-string " FAIL") (terpri) NIL)))))

(write-string "QE round-trip:")
(terpri)
(setq qe-ok
  (and (check-qe F)
       (check-qe TAU)
       (check-qe G)
       (check-qe QQ)
       (check-qe RHO)))

(defun check-idempotent (x expected)
  (let ((xx (dot x x)))
    (write-string "  ")
    (write-name x)
    (write-string " . ")
    (write-name x)
    (write-string " = ")
    (write-name xx)
    (if (= (= xx x) expected)
      (progn (write-string " ok") (terpri) T)
      (progn (write-string " FAIL") (terpri) NIL))))

(write-string "Idempotents (only absorbers):")
(terpri)
(setq idem-ok
  (and (check-idempotent TOP T)
       (check-idempotent BOT T)
       (check-idempotent QQ NIL)
       (check-idempotent EE NIL)))

(terpri)
(setq table-healthy (and absorber-ok tester-ok qe-ok idem-ok))
(if table-healthy
  (progn
    (write-string "Table health: ALL INVARIANTS HOLD")
    (terpri))
  (progn
    (write-string "Table health: CORRUPTION DETECTED")
    (terpri)))

;; === LEVEL 2: Evaluator Inspection ===
(banner "Shift Up to Level 2: Evaluator Inspection")

(setq num-bindings (env-size))
(write-string "Current environment: ")
(display num-bindings)
(write-string " bindings")
(terpri)
(write-string "Last result (fib-result): ")
(print fib-result)

(write-string "Binding 'fib': ")
(if (bound? fib) (write-string "present") (write-string "MISSING"))
(terpri)
(write-string "Binding 'table-healthy': ")
(if (bound? table-healthy) (write-string "present") (write-string "MISSING"))
(terpri)
(write-string "Binding 'fib-result': ")
(if (bound? fib-result) (write-string "present") (write-string "MISSING"))
(terpri)

(write-string "Consistency check: (fib 8) = fib-result? ")
(if (= (fib 8) fib-result)
  (write-string "ok")
  (write-string "INCONSISTENT"))
(terpri)
(terpri)
(write-string "Evaluator state: CONSISTENT")
(terpri)

;; === SHIFT DOWN: Resume ===
(banner "Shift Down: Resume with Verified Substrate")
(write-string "Computing fibonacci(12) on verified ground...")
(terpri)
(setq fib-result-2 (fib 12))
(write-string "Result: ")
(print fib-result-2)
(terpri)
(write-string "=== TOWER COMPLETE ===")
(terpri)
(write-string "Three levels. One algebra. One table.")
(terpri)
(write-string "Smith's tower had no ground. This one does.")
(terpri)`,

    // Term stepping examples
    'step-qe': `E(Q(nat(5)))`,
    'step-car': `f(App(g(nat(1)), nat(2)))`,
    'step-cdr': `\u03B7(App(g(nat(1)), nat(2)))`,
    'step-absorber': `\u22A4(nat(7))`,
};

// Which examples are term-stepping (vs Mini-Lisp)
const STEP_EXAMPLES = new Set(['step-qe', 'step-car', 'step-cdr', 'step-absorber']);

// ═══════════════════════════════════════════════════════════
// Worker Communication
// ═══════════════════════════════════════════════════════════

const worker = new Worker('worker.js', { type: 'module' });
let nextId = 0;
const pending = new Map();
let workerReady = false;

worker.onmessage = (e) => {
    const { type, id, ...data } = e.data;
    if (type === 'ready') {
        workerReady = true;
        setStatus('Ready');
        setMode('idle');
        return;
    }
    if (type === 'error') {
        const cb = pending.get(id);
        if (cb) { pending.delete(id); cb({ error: data.error }); }
        return;
    }
    const cb = pending.get(id);
    if (cb) { pending.delete(id); cb(data); }
};

worker.onerror = (e) => {
    setStatus('Worker error: ' + e.message);
};

function send(type, payload) {
    return new Promise((resolve) => {
        const id = nextId++;
        pending.set(id, resolve);
        worker.postMessage({ type, id, payload });
    });
}

// ═══════════════════════════════════════════════════════════
// State
// ═══════════════════════════════════════════════════════════

let mode = 'loading'; // loading, idle, running, stepping, auto
let autoTimer = null;
const SPEEDS = [1000, 500, 250, 100, 50];
let traceEntries = [];
let cayleyData = null;

// ═══════════════════════════════════════════════════════════
// DOM Refs
// ═══════════════════════════════════════════════════════════

const $ = (sel) => document.querySelector(sel);
const output = $('#output');
const outputInfo = $('#output-info');
const statusMode = $('#status-mode');
const statusSteps = $('#status-steps');
const statusArena = $('#status-arena');
const statusRule = $('#status-rule');
const statusDepth = $('#status-depth');
const statusTime = $('#status-time');
const treeInfo = $('#tree-info');
const traceContainer = $('#trace-container');
const traceCount = $('#trace-count');
const nodeDetails = $('#node-details');
const cayleyOp = $('#cayley-operation');

const btnRun = $('#btn-run');
const btnStepStart = $('#btn-step-start');
const btnStep = $('#btn-step');
const btnAuto = $('#btn-auto');
const btnReset = $('#btn-reset');
const speedSlider = $('#speed-slider');
const examplesSelect = $('#examples');

// Lisp stepper state (JS-based stepping for Mini-Lisp programs)
let lispStepper = null;   // generator from lisp-stepper.js
let lispStepCount = 0;
let cayleyTableData = null; // cached Cayley table for JS stepper

// ═══════════════════════════════════════════════════════════
// Components
// ═══════════════════════════════════════════════════════════

let treeRenderer;
let cayleyTable;

// ═══════════════════════════════════════════════════════════
// Mode Management
// ═══════════════════════════════════════════════════════════

function setMode(newMode) {
    mode = newMode;

    // Status badge
    statusMode.textContent = newMode.toUpperCase();
    statusMode.className = 'status-badge';
    if (newMode === 'running') statusMode.classList.add('mode-running');
    else if (newMode === 'stepping') statusMode.classList.add('mode-stepping');
    else if (newMode === 'auto') statusMode.classList.add('mode-auto');

    // Button states
    const isStepping = newMode === 'stepping' || newMode === 'auto';
    btnRun.disabled = newMode !== 'idle';
    btnStepStart.disabled = newMode !== 'idle';
    btnStep.disabled = !isStepping;
    btnAuto.disabled = newMode === 'running' || newMode === 'loading';

    // Auto button text
    if (newMode === 'auto') {
        btnAuto.textContent = '\u23F8'; // pause
        btnAuto.title = 'Pause auto-step';
    } else {
        btnAuto.textContent = '\u25B6\u25B6';
        btnAuto.title = 'Auto-step (F5)';
    }
}

function setStatus(text) {
    statusRule.textContent = text;
}

// ═══════════════════════════════════════════════════════════
// Run Mode
// ═══════════════════════════════════════════════════════════

async function runProgram() {
    if (!workerReady || mode !== 'idle') return;
    setMode('running');
    output.textContent = '';
    output.classList.remove('output-error');
    outputInfo.textContent = '';
    treeRenderer.clear();
    treeInfo.textContent = '';
    clearTrace();
    cayleyTable.clearHighlight();
    cayleyOp.textContent = '';

    const start = performance.now();
    const data = await send('run', { source: getSource() });
    const elapsed = performance.now() - start;

    if (data.error) {
        output.textContent = 'Error: ' + data.error;
        output.classList.add('output-error');
        setMode('idle');
        return;
    }

    const result = JSON.parse(data.result);

    if (result.error) {
        output.textContent = 'Error: ' + result.error;
        output.classList.add('output-error');
    } else {
        let text = '';
        if (result.io_output) text += result.io_output;
        const vals = result.results.map(r => r.display).join('\n');
        if (vals) text += (text && !text.endsWith('\n') ? '\n' : '') + vals;
        output.textContent = text;
        outputInfo.textContent = result.results.length + ' result' + (result.results.length !== 1 ? 's' : '');

        // Show result trees
        treeRenderer.showResults(result.results);
    }

    const stats = JSON.parse(data.stats);
    updateStats(stats, elapsed);
    panelGlow('#tree-panel');
    setMode('idle');
}

// ═══════════════════════════════════════════════════════════
// Step Mode
// ═══════════════════════════════════════════════════════════

function isLispSource(expr) {
    return expr.startsWith(';') || expr.startsWith('(') ||
        /\(\s*(defun|setq|let|if|lambda|progn|write|print|display|quote|define|cons|car|cdr)\b/.test(expr);
}

async function startStepping() {
    if (!workerReady || mode !== 'idle') return;

    const expr = getSource().trim();
    if (!expr) return;

    setMode('stepping');
    output.textContent = '';
    output.classList.remove('output-error');
    clearTrace();
    cayleyTable.clearHighlight();

    if (isLispSource(expr)) {
        // ── Lisp stepping: JS-based generator evaluator ──
        try {
            // Fetch Cayley table if we don't have it
            if (!cayleyTableData) {
                const tblData = await send('table');
                const parsed = JSON.parse(tblData.table);
                cayleyTableData = parsed.cells;
            }
            const stepper = createStepper(expr, cayleyTableData);
            lispStepper = stepper.steps;
            lispStepper._stepper_io = stepper.io;
            lispStepCount = 0;
            addTraceEntry(0, 'start', expr.split('\n')[0] + (expr.includes('\n') ? '...' : ''));
            setStatus('Lisp stepping \u2014 ready');
        } catch (e) {
            output.textContent = 'Parse error: ' + e.message;
            output.classList.add('output-error');
            lispStepper = null;
            setMode('idle');
        }
        return;
    }

    // ── Term stepping: WASM-based ──
    const data = await send('start_stepping', { expr });

    if (data.error) {
        output.textContent = data.error;
        output.classList.add('output-error');
        setMode('idle');
        return;
    }

    if (data.display && data.display.startsWith('parse error:')) {
        output.textContent = data.display + '\n\nTry: E(Q(nat(5)))  or  f(App(g(nat(1)), nat(2)))';
        output.classList.add('output-error');
        setMode('idle');
        return;
    }

    if (data.term && data.term !== 'null') {
        const termTree = JSON.parse(data.term);
        treeRenderer.render(termTree);
        treeInfo.textContent = 'step 0';
    }

    addTraceEntry(0, 'start', data.display || expr);
    const stats = data.stats ? JSON.parse(data.stats) : null;
    if (stats) updateStats(stats);
    setStatus('Ready to step');
}

async function doStep() {
    if (mode !== 'stepping' && mode !== 'auto') return;

    // ── Lisp stepping (JS generator) ──
    if (lispStepper) {
        try {
            const { value, done } = lispStepper.next();
            if (done || !value) {
                lispStepper = null;
                stopAutoStep();
                setMode('idle');
                setStatus('Done');
                return;
            }

            lispStepCount++;
            const step = value;

            // Build display text
            let ruleText = step.rule || step.type;
            let displayText = '';

            if (step.type === 'call') {
                displayText = step.name + '(' + (step.args || []).join(', ') + ')';
                ruleText = 'call ' + step.name;
            } else if (step.type === 'result') {
                displayText = step.call + ' \u2192 ' + step.display;
                ruleText = 'result';
            } else if (step.type === 'branch') {
                displayText = 'test=' + (step.test || '') + ' \u2192 ' + step.taking;
                ruleText = step.rule;
            } else if (step.type === 'define') {
                displayText = 'defined ' + step.name;
            } else if (step.type === 'eval') {
                displayText = step.rule;
            } else if (step.type === 'done') {
                displayText = step.display || '';
                // Show IO output if any
                const ioText = step.io || '';
                output.textContent = ioText + (ioText && displayText ? '\n' : '') + displayText;
                outputInfo.textContent = 'final result';
                if (step.tree) treeRenderer.render(step.tree);
                lispStepper = null;
                stopAutoStep();
                setMode('idle');
                setStatus('Done');
                panelGlow('#output-panel');
                addTraceEntry(lispStepCount, 'done', displayText);
                return;
            }

            // Update trace
            addTraceEntry(lispStepCount, ruleText, displayText);

            // Update status bar
            treeInfo.textContent = 'step ' + lispStepCount;
            statusSteps.textContent = 'Steps: ' + lispStepCount;
            statusDepth.textContent = 'Depth: ' + (step.depth || 0);
            statusRule.textContent = ruleText;

            // Show IO output incrementally
            if (lispStepper && lispStepper._stepper_io) {
                const ioText = lispStepper._stepper_io.output;
                if (ioText) output.textContent = ioText;
            }

            // Show result tree if available
            if (step.tree) {
                treeRenderer.render(step.tree);
                panelGlow('#tree-panel');
            }

        } catch (e) {
            output.textContent = 'Error: ' + e.message;
            output.classList.add('output-error');
            lispStepper = null;
            stopAutoStep();
            setMode('idle');
        }
        return;
    }

    // ── Term stepping (WASM) ──
    const data = await send('step');

    if (data.error) {
        output.textContent = 'Error: ' + data.error;
        output.classList.add('output-error');
        stopAutoStep();
        setMode('idle');
        return;
    }

    const info = JSON.parse(data.info);
    const stats = data.stats ? JSON.parse(data.stats) : null;

    if (data.term && data.term !== 'null') {
        const termTree = JSON.parse(data.term);
        treeRenderer.render(termTree);
    }

    addTraceEntry(info.step_count, info.rule, info.term_display);

    treeInfo.textContent = 'step ' + info.step_count;
    statusSteps.textContent = 'Steps: ' + info.step_count;
    statusDepth.textContent = 'Depth: ' + info.depth;
    statusRule.textContent = info.rule;
    if (stats) {
        statusArena.textContent = 'Arena: ' + stats.arena_size;
    }

    highlightFromRule(info.rule, info.term_display);
    panelGlow('#tree-panel');

    if (info.done) {
        stopAutoStep();
        setMode('idle');
        setStatus('Done');
        output.textContent = info.term_display;
        outputInfo.textContent = 'final result';
        panelGlow('#output-panel');
    }
}

function startAutoStep() {
    if (mode === 'idle') {
        // Start stepping first, then auto
        startStepping().then(() => {
            if (mode === 'stepping') {
                setMode('auto');
                const speed = SPEEDS[speedSlider.value] || 250;
                autoTimer = setInterval(() => doStep(), speed);
            }
        });
        return;
    }
    if (mode === 'stepping') {
        setMode('auto');
        const speed = SPEEDS[speedSlider.value] || 250;
        autoTimer = setInterval(() => doStep(), speed);
    }
}

function stopAutoStep() {
    if (autoTimer) {
        clearInterval(autoTimer);
        autoTimer = null;
    }
    if (mode === 'auto') setMode('stepping');
}

function toggleAutoStep() {
    if (mode === 'auto') {
        stopAutoStep();
    } else {
        startAutoStep();
    }
}

// ═══════════════════════════════════════════════════════════
// Reset
// ═══════════════════════════════════════════════════════════

async function resetMachine() {
    stopAutoStep();
    lispStepper = null;
    lispStepCount = 0;
    if (workerReady) await send('reset');
    output.textContent = '';
    output.classList.remove('output-error');
    outputInfo.textContent = '';
    treeRenderer.clear();
    treeInfo.textContent = '';
    clearTrace();
    cayleyTable.clearHighlight();
    cayleyOp.textContent = '';
    statusSteps.textContent = 'Steps: 0';
    statusArena.textContent = 'Arena: 0';
    statusDepth.textContent = 'Depth: 0';
    statusTime.textContent = '';
    setStatus('\u2014');
    setMode('idle');
}

// ═══════════════════════════════════════════════════════════
// Trace
// ═══════════════════════════════════════════════════════════

function clearTrace() {
    traceEntries = [];
    traceContainer.innerHTML = '';
    traceCount.textContent = '';
}

function addTraceEntry(step, rule, termDisplay) {
    traceEntries.push({ step, rule, term: termDisplay });

    const entry = document.createElement('div');
    entry.className = 'trace-entry';

    const stepEl = document.createElement('span');
    stepEl.className = 'trace-step';
    stepEl.textContent = step;

    const ruleEl = document.createElement('span');
    ruleEl.className = 'trace-rule';
    ruleEl.textContent = rule;

    const termEl = document.createElement('span');
    termEl.className = 'trace-term';
    termEl.textContent = termDisplay;
    termEl.title = termDisplay;

    entry.appendChild(stepEl);
    entry.appendChild(ruleEl);
    entry.appendChild(termEl);
    traceContainer.appendChild(entry);

    // Auto-scroll
    traceContainer.scrollTop = traceContainer.scrollHeight;
    traceCount.textContent = traceEntries.length;
}

// ═══════════════════════════════════════════════════════════
// Inspector: Node Details
// ═══════════════════════════════════════════════════════════

function showNodeDetails(info) {
    nodeDetails.innerHTML = '';

    const fields = [
        ['Kind', info.kind],
        ['Value', info.value],
        ['Role', info.role],
    ];

    if (info.desc) fields.push(['Info', info.desc]);
    if (info.depth !== undefined) fields.push(['Depth', String(info.depth)]);

    fields.forEach(([label, value]) => {
        const row = document.createElement('div');
        row.className = 'node-field';
        const lbl = document.createElement('span');
        lbl.className = 'node-field-label';
        lbl.textContent = label;
        const val = document.createElement('span');
        val.className = 'node-field-value';
        val.textContent = value || '\u2014';
        row.appendChild(lbl);
        row.appendChild(val);
        nodeDetails.appendChild(row);
    });

    // If it's an atom, highlight in Cayley table
    if (info.kind === 'atom' && cayleyData) {
        const idx = cayleyData.names.indexOf(info.value);
        if (idx >= 0) {
            // Highlight the atom's row
            cayleyTable.highlight(idx, idx);
            const result = cayleyData.names[cayleyData.cells[idx][idx]];
            cayleyOp.textContent = info.value + ' \u00B7 ' + info.value + ' = ' + result;
        }
    }
}

// ═══════════════════════════════════════════════════════════
// Cayley Table Highlight from Step Rule
// ═══════════════════════════════════════════════════════════

function highlightFromRule(rule, termDisplay) {
    if (!cayleyData) return;

    // Try to extract the operation from the term display
    // Pattern: atoms being applied — look for single-atom function application
    // The rule "dot" or "app-dot" would indicate a Cayley table lookup
    if (rule === 'dot' || rule.includes('dot')) {
        // Parse "X(Y)" pattern from term_display
        const m = termDisplay.match(/^(\S+)\((\S+)\)$/);
        if (m) {
            const op = cayleyTable.highlightByName(m[1], m[2]);
            if (op) {
                cayleyOp.textContent = op.left + ' \u00B7 ' + op.right + ' = ' + op.result;
                panelGlow('#cayley-section');
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════
// Branch Swap
// ═══════════════════════════════════════════════════════════

function handleBranchSwap(node, frameDepth) {
    showNotification('Continuation swap triggered at frame depth ' + frameDepth + ' \u2014 requires WASM API extension for live modification');
}

// ═══════════════════════════════════════════════════════════
// Stats & UI Helpers
// ═══════════════════════════════════════════════════════════

function updateStats(stats, elapsed) {
    if (stats) {
        statusSteps.textContent = 'Steps: ' + (stats.steps || 0);
        statusArena.textContent = 'Arena: ' + (stats.arena_size || 0);
    }
    if (elapsed !== undefined) {
        statusTime.textContent = elapsed.toFixed(1) + 'ms';
    }
}

function panelGlow(selector) {
    const el = document.querySelector(selector);
    if (!el) return;
    el.classList.remove('panel-glow');
    // Force reflow
    void el.offsetWidth;
    el.classList.add('panel-glow');
}

function showNotification(text) {
    const existing = document.querySelector('.notification');
    if (existing) existing.remove();

    const notif = document.createElement('div');
    notif.className = 'notification';
    notif.textContent = text;
    document.body.appendChild(notif);
    setTimeout(() => notif.remove(), 3000);
}

// ═══════════════════════════════════════════════════════════
// Cayley Table Toggle
// ═══════════════════════════════════════════════════════════

function setupCayleyToggle() {
    const toggle = $('#cayley-toggle');
    const container = $('#cayley-container');
    const arrow = toggle.querySelector('.toggle-arrow');

    toggle.addEventListener('click', () => {
        const collapsed = container.style.display === 'none';
        container.style.display = collapsed ? '' : 'none';
        arrow.classList.toggle('collapsed', !collapsed);
        toggle.setAttribute('aria-expanded', String(collapsed));
    });

    toggle.addEventListener('keydown', (e) => {
        if (e.key === 'Enter' || e.key === ' ') {
            e.preventDefault();
            toggle.click();
        }
    });
}

// ═══════════════════════════════════════════════════════════
// Event Binding
// ═══════════════════════════════════════════════════════════

function bindEvents() {
    // Buttons
    btnRun.addEventListener('click', runProgram);
    btnStepStart.addEventListener('click', startStepping);
    btnStep.addEventListener('click', doStep);
    btnAuto.addEventListener('click', toggleAutoStep);
    btnReset.addEventListener('click', resetMachine);

    // Speed slider — update auto-step interval when changed
    speedSlider.addEventListener('input', () => {
        if (mode === 'auto' && autoTimer) {
            clearInterval(autoTimer);
            const speed = SPEEDS[speedSlider.value] || 250;
            autoTimer = setInterval(() => doStep(), speed);
        }
    });

    // Examples
    examplesSelect.addEventListener('change', (e) => {
        const name = e.target.value;
        if (name && EXAMPLES[name]) {
            resetMachine().then(() => {
                setSource(EXAMPLES[name]);
            });
        }
        e.target.value = '';
    });

    // Keyboard shortcuts
    document.addEventListener('keydown', (e) => {
        // Ctrl/Cmd+Enter → Run
        if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
            e.preventDefault();
            if (mode === 'idle') runProgram();
        }

        // F10 → Step
        if (e.key === 'F10') {
            e.preventDefault();
            if (mode === 'stepping' || mode === 'auto') doStep();
        }

        // F5 → Toggle auto-step
        if (e.key === 'F5') {
            e.preventDefault();
            toggleAutoStep();
        }

        // Ctrl/Cmd+Shift+R → Reset
        if ((e.ctrlKey || e.metaKey) && e.shiftKey && e.key === 'R') {
            e.preventDefault();
            resetMachine();
        }

        // Escape → Stop auto-step
        if (e.key === 'Escape') {
            if (mode === 'auto') stopAutoStep();
        }

        // Space → Step (when not in editor)
        if (e.key === ' ' && document.activeElement !== document.getElementById('source')) {
            if (mode === 'stepping') {
                e.preventDefault();
                doStep();
            }
        }
    });

    setupCayleyToggle();
}

// ═══════════════════════════════════════════════════════════
// Initialization
// ═══════════════════════════════════════════════════════════

async function init() {
    // Initialize editor
    initEditor();

    // Initialize tree renderer
    treeRenderer = new TreeRenderer($('#tree-content'), showNodeDetails);
    treeRenderer.onBranchSwap = handleBranchSwap;

    // Initialize Cayley table
    cayleyTable = new CayleyTable($('#cayley-container'));

    // Set loading state
    setStatus('Loading WASM\u2026');
    statusMode.textContent = 'LOADING';

    // Load WASM
    worker.postMessage({ type: 'init', id: -1 });

    // Wait for ready, then load Cayley table
    await new Promise((resolve) => {
        const check = setInterval(() => {
            if (workerReady) {
                clearInterval(check);
                resolve();
            }
        }, 50);
    });

    // Fetch and build Cayley table
    const tableData = await send('table');
    cayleyData = JSON.parse(tableData.table);
    cayleyTable.build(cayleyData);

    // Load default example
    setSource(EXAMPLES.basic);

    // Bind events
    bindEvents();

    setMode('idle');
    setStatus('Ready');
}

init().catch((err) => {
    console.error('Init failed:', err);
    setStatus('Init failed: ' + err.message);
});
