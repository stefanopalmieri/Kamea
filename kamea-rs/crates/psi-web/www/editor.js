// editor.js — Code editor with Lisp syntax highlighting

const textarea = () => document.getElementById('source');
const lineNums = () => document.getElementById('line-numbers');
const highlight = () => document.getElementById('highlight-layer');

export function initEditor() {
    const ta = textarea();

    ta.addEventListener('input', () => { updateLineNumbers(); updateHighlight(); });
    ta.addEventListener('scroll', syncScroll);
    ta.addEventListener('keydown', handleKeydown);

    updateLineNumbers();
    updateHighlight();
}

export function getSource() {
    return textarea().value;
}

export function setSource(code) {
    textarea().value = code;
    updateLineNumbers();
    updateHighlight();
}

function updateLineNumbers() {
    const ta = textarea();
    const ln = lineNums();
    const lines = ta.value.split('\n').length;
    const nums = [];
    for (let i = 1; i <= lines; i++) nums.push(i);
    ln.textContent = nums.join('\n');
}

function syncScroll() {
    const ta = textarea();
    lineNums().scrollTop = ta.scrollTop;
    highlight().scrollTop = ta.scrollTop;
    highlight().scrollLeft = ta.scrollLeft;
}

function handleKeydown(e) {
    // Ctrl/Cmd+Enter — run (handled by app.js, but prevent default here)
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        return; // Let it bubble to app.js handler
    }

    // Tab inserts 2 spaces
    if (e.key === 'Tab') {
        e.preventDefault();
        const ta = e.target;
        const start = ta.selectionStart;
        const end = ta.selectionEnd;

        if (e.shiftKey) {
            // Outdent: remove leading 2 spaces from current line
            const before = ta.value.substring(0, start);
            const lineStart = before.lastIndexOf('\n') + 1;
            const linePrefix = ta.value.substring(lineStart, start);
            if (linePrefix.startsWith('  ')) {
                ta.value = ta.value.substring(0, lineStart) + ta.value.substring(lineStart + 2);
                ta.selectionStart = ta.selectionEnd = Math.max(lineStart, start - 2);
            }
        } else {
            ta.value = ta.value.substring(0, start) + '  ' + ta.value.substring(end);
            ta.selectionStart = ta.selectionEnd = start + 2;
        }
        updateLineNumbers();
        updateHighlight();
    }

    // Auto-close parens
    if (e.key === '(') {
        e.preventDefault();
        const ta = e.target;
        const start = ta.selectionStart;
        const end = ta.selectionEnd;
        const selected = ta.value.substring(start, end);
        ta.value = ta.value.substring(0, start) + '(' + selected + ')' + ta.value.substring(end);
        if (selected.length > 0) {
            ta.selectionStart = start;
            ta.selectionEnd = end + 2;
        } else {
            ta.selectionStart = ta.selectionEnd = start + 1;
        }
        updateLineNumbers();
        updateHighlight();
    }
}

// ── Syntax highlighting ──

const KEYWORDS = new Set([
    'if', 'cond', 'and', 'or', 'not', 'progn', 'begin',
    'let', 'lambda', 'quote',
]);
const SPECIALS = new Set([
    'defun', 'define', 'setq',
]);
const BUILTINS = new Set([
    '+', '-', '*', '/', 'mod', '=', '<', '>', '<=', '>=',
    'eq', 'equal', 'cons', 'car', 'cdr', 'list', 'null', 'atom',
    'zerop', 'numberp', '1+', '1-', 'print', 'display', 'terpri',
    'write-char', 'write-string', 'atom-name', 'dot',
    'bound?', 'env-size', 'env-keys',
]);
const ATOMS = new Set(['T', 'NIL']);

function highlightLisp(src) {
    const out = [];
    let i = 0;
    while (i < src.length) {
        const c = src[i];

        // Comment
        if (c === ';') {
            let j = i;
            while (j < src.length && src[j] !== '\n') j++;
            out.push('<span class="hl-comment">' + esc(src.slice(i, j)) + '</span>');
            i = j;
            continue;
        }

        // String
        if (c === '"') {
            let j = i + 1;
            while (j < src.length && src[j] !== '"') {
                if (src[j] === '\\') j++;
                j++;
            }
            if (j < src.length) j++; // include closing "
            out.push('<span class="hl-string">' + esc(src.slice(i, j)) + '</span>');
            i = j;
            continue;
        }

        // Parens
        if (c === '(' || c === ')') {
            out.push('<span class="hl-paren">' + c + '</span>');
            i++;
            continue;
        }

        // Quote shorthand
        if (c === "'") {
            out.push('<span class="hl-keyword">' + c + '</span>');
            i++;
            continue;
        }

        // Whitespace
        if (' \t\n\r'.includes(c)) {
            out.push(c);
            i++;
            continue;
        }

        // Token (symbol or number)
        let j = i;
        while (j < src.length && !' \t\n\r();'.includes(src[j])) j++;
        const tok = src.slice(i, j);

        if (/^-?\d+$/.test(tok)) {
            out.push('<span class="hl-number">' + esc(tok) + '</span>');
        } else if (ATOMS.has(tok.toUpperCase())) {
            out.push('<span class="hl-atom">' + esc(tok) + '</span>');
        } else if (KEYWORDS.has(tok)) {
            out.push('<span class="hl-keyword">' + esc(tok) + '</span>');
        } else if (SPECIALS.has(tok)) {
            out.push('<span class="hl-special">' + esc(tok) + '</span>');
        } else if (BUILTINS.has(tok)) {
            out.push('<span class="hl-builtin">' + esc(tok) + '</span>');
        } else {
            // Check if this token follows a defun/define — it's a function name
            const before = src.slice(0, i).trimEnd();
            if (before.endsWith('defun') || before.endsWith('define')) {
                out.push('<span class="hl-define">' + esc(tok) + '</span>');
            } else {
                out.push(esc(tok));
            }
        }
        i = j;
    }
    // Trailing newline ensures highlight layer matches textarea height
    return out.join('') + '\n';
}

function esc(s) {
    return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function updateHighlight() {
    const hl = highlight();
    if (!hl) return;
    hl.innerHTML = highlightLisp(textarea().value);
}

export function highlightMatchingParen() {
    // Handled visually by the highlight layer now
}
