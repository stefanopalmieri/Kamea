// editor.js — Code editor enhancements (line numbers, tab, paren matching)

const textarea = () => document.getElementById('source');
const lineNums = () => document.getElementById('line-numbers');

export function initEditor() {
    const ta = textarea();
    const ln = lineNums();

    ta.addEventListener('input', () => updateLineNumbers());
    ta.addEventListener('scroll', syncScroll);
    ta.addEventListener('keydown', handleKeydown);
    ta.addEventListener('click', () => highlightMatchingParen());
    ta.addEventListener('keyup', (e) => {
        if (['ArrowLeft', 'ArrowRight', 'ArrowUp', 'ArrowDown', 'Home', 'End'].includes(e.key)) {
            highlightMatchingParen();
        }
    });

    updateLineNumbers();
}

export function getSource() {
    return textarea().value;
}

export function setSource(code) {
    textarea().value = code;
    updateLineNumbers();
    clearParenHighlight();
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
    lineNums().scrollTop = textarea().scrollTop;
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
    }
}

// ── Paren matching ──

let parenHighlightEls = [];

function clearParenHighlight() {
    // We don't use overlay elements — paren matching is conceptual.
    // Could add a CSS overlay later.
}

export function highlightMatchingParen() {
    // Simple paren match: find matching paren at cursor
    const ta = textarea();
    const pos = ta.selectionStart;
    const text = ta.value;
    const ch = text[pos - 1];

    // This is a no-op for now — full overlay-based paren matching
    // requires a contenteditable or overlay div, which adds complexity.
    // The auto-close on '(' provides the essential paren assistance.
}
