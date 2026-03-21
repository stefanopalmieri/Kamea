// call-tree.js — Preact-based call stack visualization
//
// Uses virtual DOM diffing so only changed nodes are updated.
// Reuses the TreeRenderer's tn-pill CSS classes for consistent
// role-colored atoms across Run and Step modes.

import { h, render } from 'https://esm.sh/preact@10.25.4';
import { useState } from 'https://esm.sh/preact@10.25.4/hooks';

// ── Pill styling (matches tree-renderer.js) ──

const PILL_CLASSES = {
    '\u22a4': 'tn-pill-top', '\u22a5': 'tn-pill-bot',
    '\u03c4': 'tn-pill-tester', 'f': 'tn-pill-encoder',
    'g': 'tn-pill-inert', 'Q': 'tn-pill-q', 'E': 'tn-pill-e',
    '\u03c1': 'tn-pill-rho', '\u03b7': 'tn-pill-eta',
    'Y': 'tn-pill-y',
    'NIL': 'tn-pill-bot', 'T': 'tn-pill-top',
    'if': 'tn-pill-rho', 'cond': 'tn-pill-rho',
    'defun': 'tn-pill-q', 'define': 'tn-pill-q', 'lambda': 'tn-pill-q',
    'let': 'tn-pill-eta', 'setq': 'tn-pill-eta',
    '+': 'tn-pill-encoder', '-': 'tn-pill-encoder',
    '*': 'tn-pill-encoder', '/': 'tn-pill-encoder',
    '=': 'tn-pill-tester', '<': 'tn-pill-tester', '>': 'tn-pill-tester',
    'cons': 'tn-pill-inert', 'car': 'tn-pill-encoder', 'cdr': 'tn-pill-eta',
    'null': 'tn-pill-tester', 'atom': 'tn-pill-tester',
    'quote': 'tn-pill-q',
};

function pillClass(name) {
    return PILL_CLASSES[name] || 'tn-pill-inert';
}

function Pill({ value, cls }) {
    return h('span', { class: 'tn-pill ' + (cls || pillClass(value)) }, value);
}

function IntPill({ value }) {
    return h('span', { class: 'tn-pill tn-pill-int' }, String(value));
}

function ResultPill({ value }) {
    if (value === null) return Pill({ value: 'NIL' });
    if (value === true) return Pill({ value: 'T' });
    if (typeof value === 'number') return IntPill({ value });
    if (typeof value === 'string') return Pill({ value: value.length > 20 ? value.slice(0, 20) + '\u2026' : value });
    if (typeof value === 'function') return Pill({ value: '#<fn>', cls: 'tn-pill-inert' });
    if (value && value._lambda) return Pill({ value: '#<\u03bb>', cls: 'tn-pill-q' });
    if (Array.isArray(value) && value._pair) return Pill({ value: '(\u2026)', cls: 'tn-pill-inert' });
    return Pill({ value: String(value) });
}

// ── Frame component ──

function Frame({ frame, isActive, child, depth }) {
    const [collapsed, setCollapsed] = useState(false);
    const hasChild = !!child;
    const toggle = () => { if (hasChild) setCollapsed(!collapsed); };

    return h('div', { class: 'tn' + (isActive ? ' tn-current' : '') },
        // Header row
        h('div', { class: 'tn-row', onClick: toggle, style: 'cursor: pointer' },
            // Toggle arrow
            hasChild
                ? h('button', { class: 'tn-toggle', onClick: e => { e.stopPropagation(); toggle(); } },
                    h('span', { class: 'tn-arrow' + (collapsed ? '' : ' open') }, '\u25b6'))
                : h('span', { class: 'tn-arrow leaf', style: 'width:10px;display:inline-block;font-size:8px;color:var(--text-dim)' }, '\u00b7'),

            // Function name as pill
            Pill({ value: (isActive ? '\u25b6 ' : '') + (frame.name || '?') }),

            // Args as pills
            ...(frame.args || []).map((a, i) => {
                if (typeof a === 'string' && !isNaN(Number(a))) return IntPill({ value: a, key: 'a' + i });
                return Pill({ value: String(a), key: 'a' + i });
            }),

            // Return value
            frame.result !== undefined
                ? h('span', { class: 'tn-field-label', style: 'margin:0 2px' }, '\u2192',
                    h('span', { style: 'margin-left:4px' }, ResultPill({ value: frame.result })))
                : null,
        ),

        // Children
        !collapsed && hasChild
            ? h('div', { class: 'tn-children' }, child)
            : null,
    );
}

// ── Stack tree ──

function StackTree({ stack }) {
    if (!stack || stack.length === 0) {
        return h('div', { class: 'cs-empty', style: 'color:var(--text-dim);font-style:italic;padding:8px' },
            'Click Start then Step to begin');
    }

    let node = null;
    for (let i = stack.length - 1; i >= 0; i--) {
        node = h(Frame, {
            frame: stack[i],
            isActive: i === stack.length - 1,
            child: node,
            depth: i,
            key: i,
        });
    }
    return node;
}

// ── Public API ──

let currentContainer = null;

export function renderCallStack(container, stack) {
    currentContainer = container;
    render(h(StackTree, { stack: stack ? [...stack] : [] }), container);
}

export function clearCallStack(container) {
    render(null, container || currentContainer);
}
