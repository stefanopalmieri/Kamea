// lisp-stepper.js — Iterative stepping Lisp evaluator
//
// Uses an explicit continuation stack (trampoline) instead of recursive
// generators to avoid blowing the JS call stack on deeply nested programs
// like the reflective tower (~4 levels of meta-circular interpretation).

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
            while (j < src.length && src[j] !== '"') {
                if (src[j] === '\\') j++;
                j++;
            }
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
        if (items.length > 6) return '(' + items.slice(0, 5).map(displayVal).join(' ') + ' ...)';
        return '(' + items.map(displayVal).join(' ') + ')';
    }
    return String(v);
}

// ── Tree snapshot (for Preact call tree) ──

function valToTree(v) {
    if (v === NIL) return { kind: 'atom', value: 'NIL' };
    if (v === T) return { kind: 'atom', value: 'T' };
    if (typeof v === 'number') return { kind: 'int', value: String(v), int_value: v };
    if (typeof v === 'string') return { kind: 'atom', value: v };
    if (typeof v === 'function') return { kind: 'atom', value: '#<builtin>' };
    if (v && v._lambda) return { kind: 'atom', value: '#<lambda>' };
    if (Array.isArray(v) && v._pair) {
        const items = listToArray(v);
        return { kind: 'list', list_items: items.slice(0, 8).map(valToTree), value: displayVal(v) };
    }
    return { kind: 'atom', value: String(v) };
}

function stackToTree(stack) {
    if (stack.length === 0) return { kind: 'atom', value: '\u2014' };
    let node = null;
    for (let i = stack.length - 1; i >= 0; i--) {
        const frame = stack[i];
        const isActive = (i === stack.length - 1);
        const items = [];
        const label = { kind: 'atom', value: (isActive ? '\u25b6 ' : '') + (frame.name || 'eval') };
        items.push(label);
        if (frame.args) {
            for (const a of frame.args) {
                items.push(typeof a === 'number'
                    ? { kind: 'int', value: String(a), int_value: a }
                    : { kind: 'atom', value: String(a) });
            }
        }
        if (frame.result !== undefined) {
            items.push({ kind: 'atom', value: '\u2192' });
            items.push(valToTree(frame.result));
        }
        if (node) items.push(node);
        node = { kind: 'list', list_items: items, value: frame.name || 'eval' };
    }
    return node;
}

// ── Atom names ──

const ATOM_NAMES = [
    '\u22a4', '\u22a5', 'f', '\u03c4', 'g', '5',
    'Q', 'E', '\u03c1', '\u03b7', 'Y', '11',
    '12', '13', '14', '15',
];

// ── Stepper (iterative trampoline) ──

export function createStepper(source, cayleyTable) {
    const exprs = parseAll(source);
    const io = { output: '' };
    const callStack = [];
    const env = makeBuiltins(cayleyTable, io);
    return {
        steps: runStepper(exprs, env, io, callStack),
        stack: callStack,
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
        'write-char': (a) => { if (typeof a === 'number') io.output += String.fromCharCode(a); return a; },
        'write-string': (a) => {
            if (typeof a === 'string') { io.output += a; }
            else if (Array.isArray(a) && a._pair) {
                const chars = listToArray(a);
                io.output += chars.map(c => typeof c === 'number' ? String.fromCharCode(c) : '').join('');
            }
            return a;
        },
        'atom-name': (a) => {
            if (typeof a === 'number' && a >= 0 && a < 16)
                return toList([...ATOM_NAMES[a]].map(c => c.charCodeAt(0)));
            return NIL;
        },
        'length': (lst) => { let n = 0; while (lst !== NIL && Array.isArray(lst) && lst._pair) { n++; lst = lst[1]; } return n; },
        'nth': (n, lst) => { for (let i = 0; i < n && lst !== NIL && Array.isArray(lst); i++) lst = lst[1]; return (lst !== NIL && Array.isArray(lst)) ? lst[0] : NIL; },
        'assoc': (key, alist) => {
            while (alist !== NIL && Array.isArray(alist) && alist._pair) {
                const pair = alist[0];
                if (Array.isArray(pair) && pair._pair && pair[0] === key) return pair;
                alist = alist[1];
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

// ── Iterative evaluator with explicit continuation stack ──
//
// Instead of recursive generator calls (yield* evalExpr(...)), we use
// an explicit stack of continuations. Each step pops one continuation,
// processes it, and pushes new ones. This keeps the JS call stack flat
// regardless of Lisp nesting depth.
//
// Continuation types (what to do with a value):
//   ['done']                      — final result
//   ['expr', expr, env]           — evaluate this expression
//   ['progn', exprs, idx, env]    — evaluate exprs[idx], then next
//   ['if-test', expr, env]        — test evaluated, decide branch
//   ['if-branch', expr, env, taking] — evaluate chosen branch
//   ['args', head, exprs, idx, acc, env] — evaluate args one by one
//   ['apply', head, fn, args, env] — apply fn to args
//   ['let-binds', binds, idx, newEnv, origEnv, body] — eval let bindings
//   ['let-body', body, newEnv]     — eval let body
//   ['setq', name, env]           — assign result to name
//   ['return-call', name]         — pop call stack after return

function* runStepper(exprs, env, io, callStack) {
    // Continuation stack: each entry is a continuation frame
    const K = [];
    let val = NIL;  // current value being threaded through continuations

    // Seed: evaluate each top-level expression in sequence
    for (let i = exprs.length - 1; i >= 0; i--) {
        K.push(['expr', exprs[i], env]);
    }

    while (K.length > 0) {
        const frame = K.pop();
        const type = frame[0];

        if (type === 'expr') {
            const [, expr, env] = frame;
            val = evalAtom(expr, env, io, K, callStack);
            if (val !== NEED_MORE) continue;
            // evalAtom pushed continuations onto K; loop will process them
            continue;
        }

        if (type === 'if-decide') {
            const [, expr, env] = frame;
            const test = val;
            const branch = isTruthy(test) ? 'then' : 'else';
            const branchExpr = branch === 'then' ? expr[2] : (expr[3] !== undefined ? expr[3] : NIL);
            callStack.push({ name: 'if', rule: 'if-' + branch });
            yield { type: 'branch', rule: 'if-' + branch, test: displayVal(test), taking: branch, depth: callStack.length, tree: stackToTree(callStack) };
            callStack.pop();
            if (branchExpr === NIL || branchExpr === undefined) { val = NIL; continue; }
            K.push(['expr', branchExpr, env]);
            continue;
        }

        if (type === 'cond-test') {
            const [, clauses, idx, env] = frame;
            if (isTruthy(val)) {
                K.push(['expr', clauses[idx][1], env]);
            } else if (idx + 1 < clauses.length) {
                K.push(['cond-test', clauses, idx + 1, env]);
                K.push(['expr', clauses[idx + 1][0], env]);
            } else {
                val = NIL;
            }
            continue;
        }

        if (type === 'args') {
            const [, headName, exprs, idx, acc, env] = frame;
            acc.push(val);
            if (idx < exprs.length) {
                K.push(['args', headName, exprs, idx + 1, acc, env]);
                K.push(['expr', exprs[idx], env]);
            } else {
                // All args evaluated. Now evaluate head.
                K.push(['apply', headName, null, acc, env]);
                K.push(['expr', headName, env]);
            }
            continue;
        }

        if (type === 'apply') {
            const [, headName, , args, env] = frame;
            const fn = val;
            if (typeof fn === 'function') {
                const fnName = typeof headName === 'string' ? headName : '?';
                val = fn(...args);
                callStack.push({ name: fnName, args: args.map(displayVal), result: val });
                yield { type: 'result', rule: 'builtin', display: displayVal(val),
                    call: fnName + '(' + args.map(displayVal).join(', ') + ')',
                    depth: callStack.length, tree: stackToTree(callStack) };
                callStack.pop();
                continue;
            }
            if (fn && fn._lambda) {
                const callEnv = { ...fn.env };
                for (let i = 0; i < fn.params.length; i++) callEnv[fn.params[i]] = args[i];
                const name = fn.name || '#<lambda>';
                callStack.push({ name, args: args.map(displayVal) });
                yield { type: 'call', rule: 'call ' + name, depth: callStack.length, tree: stackToTree(callStack) };
                K.push(['return-call', name]);
                K.push(['expr', fn.body, callEnv]);
                continue;
            }
            throw new Error('not callable: ' + displayVal(fn));
        }

        if (type === 'return-call') {
            const [, name] = frame;
            if (callStack.length > 0) {
                callStack[callStack.length - 1].result = val;
                yield { type: 'return', rule: name + ' \u2192 ' + displayVal(val), display: displayVal(val), depth: callStack.length, tree: stackToTree(callStack) };
                callStack.pop();
            }
            continue;
        }

        if (type === 'progn') {
            const [, exprs, idx, env] = frame;
            // val has result of previous expr (ignored except for last)
            if (idx < exprs.length) {
                K.push(['progn', exprs, idx + 1, env]);
                K.push(['expr', exprs[idx], env]);
            }
            // else val stays as the last result
            continue;
        }

        if (type === 'let-binds') {
            const [, binds, idx, newEnv, origEnv, body] = frame;
            if (idx > 0) newEnv[binds[idx - 1][0]] = val;  // store previous binding result
            if (idx < binds.length) {
                K.push(['let-binds', binds, idx + 1, newEnv, origEnv, body]);
                K.push(['expr', binds[idx][1], origEnv]);
            } else {
                K.push(['expr', body, newEnv]);
            }
            continue;
        }

        if (type === 'setq') {
            const [, name, env] = frame;
            env[name] = val;
            continue;
        }

        if (type === 'and-next') {
            const [, exprs, idx, env] = frame;
            if (!isTruthy(val)) { val = NIL; continue; }
            if (idx < exprs.length) {
                K.push(['and-next', exprs, idx + 1, env]);
                K.push(['expr', exprs[idx], env]);
            }
            // else val stays as the last truthy result
            continue;
        }

        if (type === 'or-next') {
            const [, exprs, idx, env] = frame;
            if (isTruthy(val)) continue; // val is the result
            if (idx < exprs.length) {
                K.push(['or-next', exprs, idx + 1, env]);
                K.push(['expr', exprs[idx], env]);
            } else {
                val = NIL;
            }
            continue;
        }
    }

    yield { type: 'done', result: val, display: displayVal(val), tree: valToTree(val), io: io.output };
}

// Sentinel: evalAtom returns this when it pushed continuations
const NEED_MORE = Symbol('NEED_MORE');

// Evaluate atomic expressions or push continuations for compound ones.
// Returns the value directly for atoms, or NEED_MORE if continuations were pushed.
function evalAtom(expr, env, io, K, callStack) {
    // String literal
    if (expr && typeof expr === 'object' && '_str' in expr) return expr._str;

    // Number
    if (typeof expr === 'number') return expr;

    // Symbol
    if (typeof expr === 'string') {
        const upper = expr.toUpperCase();
        if (upper === 'NIL') return NIL;
        if (upper === 'T') return T;
        if (expr in env) return env[expr];
        throw new Error('unbound: ' + expr);
    }

    // Empty list
    if (!Array.isArray(expr) || expr.length === 0) return NIL;

    const head = expr[0];

    // ── Special forms ──

    if (head === 'quote') return quoteDatum(expr[1]);

    if (head === 'bound?') {
        const name = expr[1];
        return (typeof name === 'string' && name in env) ? T : NIL;
    }

    if (head === 'if') {
        K.push(['if-decide', expr, env]);
        K.push(['expr', expr[1], env]);
        return NEED_MORE;
    }

    if (head === 'cond') {
        const clauses = expr.slice(1);
        if (clauses.length === 0) return NIL;
        K.push(['cond-test', clauses, 0, env]);
        K.push(['expr', clauses[0][0], env]);
        return NEED_MORE;
    }

    if (head === 'defun') {
        const name = expr[1];
        const params = expr[2];
        const body = expr.length === 4 ? expr[3] : ['progn', ...expr.slice(3)];
        const fn = { _lambda: true, params, body, env, name };
        env[name] = fn;
        // Don't yield for defuns to reduce noise — too many in metacircular evaluator
        return NIL;
    }

    if (head === 'define') {
        if (Array.isArray(expr[1])) {
            const name = expr[1][0];
            const params = expr[1].slice(1);
            const body = expr.length === 3 ? expr[2] : ['progn', ...expr.slice(2)];
            const fn = { _lambda: true, params, body, env, name };
            env[name] = fn;
            return NIL;
        }
        K.push(['setq', expr[1], env]);
        K.push(['expr', expr[2], env]);
        return NEED_MORE;
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
        if (bindings.length === 0) {
            K.push(['expr', body, newEnv]);
        } else {
            K.push(['let-binds', bindings, 0, newEnv, env, body]);
        }
        return NEED_MORE;
    }

    if (head === 'setq') {
        K.push(['setq', expr[1], env]);
        K.push(['expr', expr[2], env]);
        return NEED_MORE;
    }

    if (head === 'progn' || head === 'begin') {
        const body = expr.slice(1);
        if (body.length === 0) return NIL;
        if (body.length === 1) { K.push(['expr', body[0], env]); return NEED_MORE; }
        K.push(['progn', body, 1, env]);
        K.push(['expr', body[0], env]);
        return NEED_MORE;
    }

    if (head === 'and') {
        const parts = expr.slice(1);
        if (parts.length === 0) return T;
        K.push(['and-next', parts, 1, env]);
        K.push(['expr', parts[0], env]);
        return NEED_MORE;
    }

    if (head === 'or') {
        const parts = expr.slice(1);
        if (parts.length === 0) return NIL;
        K.push(['or-next', parts, 1, env]);
        K.push(['expr', parts[0], env]);
        return NEED_MORE;
    }

    // ── Application: evaluate args first, then head, then apply ──
    const argExprs = expr.slice(1);
    if (argExprs.length === 0) {
        // No args — just evaluate head and apply
        K.push(['apply', head, null, [], env]);
        K.push(['expr', head, env]);
    } else {
        // Evaluate first arg, then continue with rest
        K.push(['args', head, argExprs, 1, [], env]);
        K.push(['expr', argExprs[0], env]);
    }
    return NEED_MORE;
}

function quoteDatum(expr) {
    if (typeof expr === 'number') return expr;
    if (typeof expr === 'string') {
        const u = expr.toUpperCase();
        if (u === 'NIL') return NIL;
        if (u === 'T') return T;
        return expr;
    }
    if (Array.isArray(expr)) return toList(expr.map(quoteDatum));
    return NIL;
}
