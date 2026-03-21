// call-tree.js — Preact-based call stack visualization
//
// Uses virtual DOM diffing so only changed nodes are updated.
// No full DOM rebuild, no blinking.

import { h, render } from 'https://esm.sh/preact@10.25.4';
import { useState } from 'https://esm.sh/preact@10.25.4/hooks';

// ── Frame component ──
// Each call stack frame shows: name, args, result (if returned).
// Child frames are nested inside. Active frame has ▶ marker.

function Frame({ frame, isActive, child, depth }) {
    const [collapsed, setCollapsed] = useState(false);

    const hasBody = child || (frame.expr && Array.isArray(frame.expr));
    const toggle = () => { if (hasBody) setCollapsed(!collapsed); };

    return h('div', {
        class: 'cs-frame' + (isActive ? ' cs-active' : '') + (depth === 0 ? ' cs-root' : ''),
    },
        h('div', { class: 'cs-header', onClick: toggle },
            hasBody
                ? h('span', { class: 'cs-arrow' + (collapsed ? '' : ' open') }, '\u25b6')
                : h('span', { class: 'cs-arrow cs-leaf' }, '\u00b7'),
            h('span', { class: 'cs-name' }, frame.name || '?'),
            ...(frame.args || []).map((a, i) =>
                h('span', { class: 'cs-arg', key: 'a' + i }, a)
            ),
            frame.result !== undefined ? [
                h('span', { class: 'cs-result-arrow', key: 'ra' }, ' \u2192 '),
                h('span', { class: 'cs-result-val', key: 'rv' }, displayShort(frame.result)),
            ] : null,
        ),
        !collapsed && child
            ? h('div', { class: 'cs-body' }, child)
            : null,
    );
}

function displayShort(v) {
    if (v === null) return 'NIL';
    if (v === true) return 'T';
    if (typeof v === 'number') return String(v);
    if (typeof v === 'string') return v.length > 20 ? v.slice(0, 20) + '\u2026' : v;
    if (typeof v === 'function') return '#<fn>';
    if (v && v._lambda) return '#<\u03bb>';
    return String(v);
}

// ── Stack tree ──
// Build nested frames from the stack array (index 0 = outermost).

function StackTree({ stack }) {
    if (!stack || stack.length === 0) {
        return h('div', { class: 'cs-empty' }, 'No active evaluation');
    }

    // Build inside-out: innermost frame has no children
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
