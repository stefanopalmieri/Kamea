// lisp-stepper.js — Generator-based stepping Lisp evaluator
//
// A minimal Lisp evaluator that yields at each reduction step,
// producing tree snapshots suitable for the existing TreeRenderer.
// Uses the Cayley table from WASM for the `dot` builtin.

// ── Parser ──

function tokenize(src) {
    const toks = [];
    let i = 0;
    while (i < src.length) {
        const c = src[i];
        if (c === ';') { while (i < src.length && src[i] !== '\n') i++; continue; }
        if (' \t\n\r'.includes(c)) { i++; continue; }
        if (c === '(' || c === ')') { toks.push(c); i++; continue; }
        if (c === "'") { toks.push("'"); i++; continue; }
        if (c === '"') {
            let j = i + 1;
            while (j < src.length && src[j] !== '"') j++;
            toks.push(src.slice(i, j + 1)); i = j + 1; continue;
        }
        let j = i;
        while (j < src.length && !' \t\n\r();'.includes(src[j])) j++;
        toks.push(src.slice(i, j)); i = j;
    }
    return toks;
}

function parse(toks, pos) {
    if (pos >= toks.length) throw new Error('unexpected end');
    const t = toks[pos];
    if (t === "'") { const [e, p] = parse(toks, pos + 1); return [['quote', e], p]; }
    if (t === '(') {
        pos++;
        const items = [];
        while (pos < toks.length && toks[pos] !== ')') {
            const [e, p] = parse(toks, pos);
            items.push(e); pos = p;
        }
        if (pos >= toks.length) throw new Error('missing )');
        return [items, pos + 1];
    }
    if (t === ')') throw new Error('unexpected )');
    // String literal
    if (t.startsWith('"') && t.endsWith('"')) {
        return [{ _str: t.slice(1, -1).replace(/\\n/g, '\n').replace(/\\t/g, '\t').replace(/\\\\/g, '\\') }, pos + 1];
    }
    const n = Number(t);
    if (!isNaN(n) && t !== '') return [n, pos + 1];
    return [t, pos + 1];
}

function parseAll(src) {
    const toks = tokenize(src);
    const exprs = [];
    let pos = 0;
    while (pos < toks.length) { const [e, p] = parse(toks, pos); exprs.push(e); pos = p; }
    return exprs;
}

// ── Values ──

const NIL = null;
const T = true;

function isTruthy(v) { return v !== NIL; }
function isNum(v) { return typeof v === 'number'; }
function isSym(v) { return typeof v === 'string'; }
function isList(v) { return Array.isArray(v) && v._pair; }

function cons(a, b) { const p = [a, b]; p._pair = true; return p; }
function car(p) { return Array.isArray(p) ? p[0] : null; }
function cdr(p) { return Array.isArray(p) ? p[1] : null; }

function toList(arr) {
    let r = NIL;
    for (let i = arr.length - 1; i >= 0; i--) r = cons(arr[i], r);
    return r;
}

function listToArray(v) {
    const a = [];
    while (v !== NIL && Array.isArray(v)) { a.push(v[0]); v = v[1]; }
    return a;
}

function displayVal(v) {
    if (v === NIL) return 'NIL';
    if (v === T) return 'T';
    if (typeof v === 'number') return String(v);
    if (typeof v === 'string') return '"' + v + '"';
    if (typeof v === 'function') return '#<builtin>';
    if (v && v._lambda) return '#<lambda>';
    if (v && typeof v === 'object' && '_str' in v) return '"' + v._str + '"';
    if (Array.isArray(v) && v._pair) {
        const items = listToArray(v);
        return '(' + items.map(displayVal).join(' ') + ')';
    }
    return String(v);
}

// ── Tree snapshot (for TreeRenderer) ──

function valToTree(v) {
    if (v === NIL) return { kind: 'atom', value: 'NIL' };
    if (v === T) return { kind: 'atom', value: 'T' };
    if (typeof v === 'number') return { kind: 'int', value: String(v), int_value: v };
    if (typeof v === 'string') return { kind: 'atom', value: v };
    if (typeof v === 'function') return { kind: 'atom', value: '#<builtin>' };
    if (v && v._lambda) return { kind: 'atom', value: '#<lambda>' };
    if (Array.isArray(v) && v._pair) {
        const items = listToArray(v);
        return {
            kind: 'list',
            list_items: items.map(valToTree),
            value: '(' + items.map(displayVal).join(' ') + ')'
        };
    }
    return { kind: 'atom', value: String(v) };
}

function exprToTree(expr, activeId, nextId) {
    const id = nextId.val++;
    const active = (id === activeId);

    if (typeof expr === 'number') {
        return { kind: 'int', value: String(expr), int_value: expr, _active: active, _id: id };
    }
    if (typeof expr === 'string') {
        return { kind: 'atom', value: expr, _active: active, _id: id };
    }
    if (Array.isArray(expr) && !expr._pair) {
        // S-expression list: first element is operator
        const children = expr.map(e => exprToTree(e, activeId, nextId));
        return {
            kind: 'list',
            list_items: children,
            value: '(' + expr.map(e => typeof e === 'number' ? e : (typeof e === 'string' ? e : '...')).join(' ') + ')',
            _active: active,
            _id: id
        };
    }
    return { kind: 'atom', value: displayVal(expr), _active: active, _id: id };
}

// ── Stepping evaluator ──

// Atom names matching psi-core NAMES
const ATOM_NAMES = [
    '\u22a4', '\u22a5', 'f', '\u03c4', 'g', '5',
    'Q', 'E', '\u03c1', '\u03b7', 'Y', '11',
    '12', '13', '14', '15',
];

export function createStepper(source, cayleyTable) {
    const exprs = parseAll(source);
    const io = { output: '' };
    const env = makeBuiltins(cayleyTable, io);
    return {
        steps: evalProgram(exprs, env, io),
        source,
        io,
    };
}

function makeBuiltins(table, io) {
    const env = {
        '+': (a, b) => a + b,
        '-': (a, b) => Math.max(0, a - b),
        '*': (a, b) => a * b,
        '/': (a, b) => Math.floor(a / b),
        'mod': (a, b) => a % b,
        '=': (a, b) => a === b ? T : NIL,
        'eq': (a, b) => a === b ? T : NIL,
        'equal': (a, b) => a === b ? T : NIL,
        '<': (a, b) => a < b ? T : NIL,
        '>': (a, b) => a > b ? T : NIL,
        '<=': (a, b) => a <= b ? T : NIL,
        '>=': (a, b) => a >= b ? T : NIL,
        'cons': (a, b) => cons(a, b),
        'car': (a) => car(a),
        'cdr': (a) => cdr(a),
        'list': (...args) => toList(args),
        'null': (a) => a === NIL ? T : NIL,
        'atom': (a) => (typeof a === 'number' || a === T || a === NIL || typeof a === 'string') ? T : NIL,
        'zerop': (a) => a === 0 ? T : NIL,
        'not': (a) => a === NIL ? T : NIL,
        '1+': (a) => a + 1,
        '1-': (a) => Math.max(0, a - 1),
        'numberp': (a) => typeof a === 'number' ? T : NIL,
        'print': (a) => { io.output += displayVal(a) + '\n'; return a; },
        'display': (a) => { io.output += displayVal(a); return a; },
        'terpri': () => { io.output += '\n'; return NIL; },
        'write-char': (a) => {
            if (typeof a === 'number') io.output += String.fromCharCode(a);
            return a;
        },
        'write-string': (a) => {
            if (typeof a === 'string') {
                io.output += a;
            } else if (Array.isArray(a) && a._pair) {
                // List of char codes
                const chars = listToArray(a);
                io.output += chars.map(c => typeof c === 'number' ? String.fromCharCode(c) : '').join('');
            }
            return a;
        },
        'atom-name': (a) => {
            if (typeof a === 'number' && a >= 0 && a < 16) {
                const name = ATOM_NAMES[a];
                return toList([...name].map(c => c.charCodeAt(0)));
            }
            return NIL;
        },
        'env-size': () => Object.keys(env).length,
        'env-keys': () => toList(Object.keys(env).map(k => toList([...k].map(c => c.charCodeAt(0))))),
    };
    if (table) {
        env['dot'] = (a, b) => {
            if (typeof a === 'number' && typeof b === 'number' && a >= 0 && a < 16 && b >= 0 && b < 16)
                return table[a][b];
            return NIL;
        };
    }
    return env;
}

function* evalProgram(exprs, env, io) {
    let result = NIL;
    for (const expr of exprs) {
        result = yield* evalExpr(expr, env, 0, io);
    }
    yield { type: 'done', result, display: displayVal(result), tree: valToTree(result), io: io.output };
}

function* evalExpr(expr, env, depth, io) {
    // String literals
    if (expr && typeof expr === 'object' && '_str' in expr) {
        return expr._str;
    }

    // Atoms
    if (typeof expr === 'number') {
        return expr;
    }

    if (typeof expr === 'string') {
        const upper = expr.toUpperCase();
        if (upper === 'NIL') return NIL;
        if (upper === 'T') return T;
        if (expr in env) return env[expr];
        throw new Error('unbound: ' + expr);
    }

    if (!Array.isArray(expr) || expr.length === 0) return NIL;

    const head = expr[0];

    // ── Special forms ──

    if (head === 'quote') return quoteDatum(expr[1]);

    if (head === 'if') {
        yield { type: 'eval', rule: 'if-test', expr: expr, depth, focus: expr[1] };
        const test = yield* evalExpr(expr[1], env, depth + 1, io);
        const branch = isTruthy(test) ? 'then' : 'else';
        const branchExpr = branch === 'then' ? expr[2] : (expr[3] || NIL);
        yield { type: 'branch', rule: 'if-' + branch, test: displayVal(test), expr: expr, depth, taking: branch };
        if (branchExpr === undefined || branchExpr === NIL) return NIL;
        return yield* evalExpr(branchExpr, env, depth + 1, io);
    }

    if (head === 'cond') {
        for (let i = 1; i < expr.length; i++) {
            const clause = expr[i];
            const test = yield* evalExpr(clause[0], env, depth + 1, io);
            if (isTruthy(test)) {
                yield { type: 'branch', rule: 'cond-match', depth, taking: i };
                return yield* evalExpr(clause[1], env, depth + 1, io);
            }
        }
        return NIL;
    }

    if (head === 'defun') {
        const name = expr[1];
        const params = expr[2];
        const body = expr.length === 4 ? expr[3] : ['progn', ...expr.slice(3)];
        const fn = { _lambda: true, params, body, env: { ...env }, name };
        fn.env[name] = fn; // self-reference for recursion
        env[name] = fn;
        yield { type: 'define', rule: 'defun', name, depth };
        return NIL;
    }

    if (head === 'define') {
        if (Array.isArray(expr[1])) {
            const name = expr[1][0];
            const params = expr[1].slice(1);
            const body = expr.length === 3 ? expr[2] : ['progn', ...expr.slice(2)];
            const fn = { _lambda: true, params, body, env: { ...env }, name };
            fn.env[name] = fn;
            env[name] = fn;
            yield { type: 'define', rule: 'define-fn', name, depth };
            return NIL;
        }
        const val = yield* evalExpr(expr[2], env, depth + 1, io);
        env[expr[1]] = val;
        return NIL;
    }

    if (head === 'lambda') {
        const params = expr[1];
        const body = expr.length === 3 ? expr[2] : ['progn', ...expr.slice(2)];
        return { _lambda: true, params, body, env: { ...env } };
    }

    if (head === 'let') {
        const bindings = expr[1];
        const body = expr.length === 3 ? expr[2] : ['progn', ...expr.slice(2)];
        const newEnv = { ...env };
        for (const [name, valExpr] of bindings) {
            newEnv[name] = yield* evalExpr(valExpr, env, depth + 1, io);
        }
        yield { type: 'eval', rule: 'let-body', depth };
        return yield* evalExpr(body, newEnv, depth + 1, io);
    }

    if (head === 'setq') {
        const val = yield* evalExpr(expr[2], env, depth + 1, io);
        env[expr[1]] = val;
        return val;
    }

    if (head === 'progn' || head === 'begin') {
        let result = NIL;
        for (let i = 1; i < expr.length; i++) {
            result = yield* evalExpr(expr[i], env, depth + 1, io);
        }
        return result;
    }

    if (head === 'and') {
        let result = T;
        for (let i = 1; i < expr.length; i++) {
            result = yield* evalExpr(expr[i], env, depth + 1, io);
            if (!isTruthy(result)) return NIL;
        }
        return result;
    }

    if (head === 'or') {
        for (let i = 1; i < expr.length; i++) {
            const r = yield* evalExpr(expr[i], env, depth + 1, io);
            if (isTruthy(r)) return r;
        }
        return NIL;
    }

    // ── Application ──

    yield { type: 'eval', rule: 'apply', expr, depth, focus: head };
    const fn = yield* evalExpr(head, env, depth + 1, io);
    const args = [];
    for (let i = 1; i < expr.length; i++) {
        args.push(yield* evalExpr(expr[i], env, depth + 1, io));
    }

    // Builtin
    if (typeof fn === 'function') {
        const result = fn(...args);
        yield {
            type: 'result', rule: 'builtin',
            expr, result, display: displayVal(result), depth,
            call: displayVal(head) + '(' + args.map(displayVal).join(', ') + ')',
            tree: valToTree(result),
        };
        return result;
    }

    // Lambda / defun
    if (fn && fn._lambda) {
        const callEnv = { ...fn.env };
        for (let i = 0; i < fn.params.length; i++) {
            callEnv[fn.params[i]] = args[i];
        }
        yield {
            type: 'call', rule: 'call',
            name: fn.name || '#<lambda>',
            args: args.map(displayVal),
            depth,
        };
        return yield* evalExpr(fn.body, callEnv, depth + 1, io);
    }

    throw new Error('not callable: ' + displayVal(fn));
}

function quoteDatum(expr) {
    if (typeof expr === 'number') return expr;
    if (typeof expr === 'string') {
        const u = expr.toUpperCase();
        if (u === 'NIL') return NIL;
        if (u === 'T') return T;
        return expr; // symbol
    }
    if (Array.isArray(expr)) return toList(expr.map(quoteDatum));
    return NIL;
}
