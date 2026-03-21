// tree-renderer.js — Continuation tree visualization with role-colored atoms

// Atom name → pill CSS class
const PILL_CLASSES = {
    '\u22a4': 'tn-pill-top',       // ⊤
    '\u22a5': 'tn-pill-bot',       // ⊥
    '\u03c4': 'tn-pill-tester',    // τ
    'f':      'tn-pill-encoder',
    'g':      'tn-pill-inert',
    'X':      'tn-pill-inert',
    'Q':      'tn-pill-q',
    'E':      'tn-pill-e',
    '\u03c1': 'tn-pill-rho',       // ρ
    '\u03b7': 'tn-pill-eta',       // η
    'Y':      'tn-pill-y',
};

// Role descriptions for the inspector
const ROLE_DESC = {
    '\u22a4': { role: 'absorber', desc: 'Top absorber \u2014 annihilates everything' },
    '\u22a5': { role: 'absorber', desc: 'Bottom absorber \u2014 annihilates everything' },
    '\u03c4': { role: 'tester', desc: 'Tester \u2014 classifies atoms into \u22a4/\u22a5' },
    'f':      { role: 'encoder', desc: 'Encoder (car) \u2014 extracts first component' },
    'g':      { role: 'encoder', desc: 'Encoder (cons) \u2014 builds pairs' },
    'Q':      { role: 'operator', desc: 'Quote \u2014 freezes (wraps) terms' },
    'E':      { role: 'operator', desc: 'Eval \u2014 unfreezes (unwraps) terms' },
    '\u03c1': { role: 'operator', desc: 'Conditional \u2014 branches on structure' },
    '\u03b7': { role: 'operator', desc: 'Cdr \u2014 extracts second component' },
    'Y':      { role: 'operator', desc: 'Fixed-point combinator' },
    'X':      { role: 'inert', desc: 'Inert substrate element' },
};

function atomPillClass(name) {
    return PILL_CLASSES[name] || 'tn-pill-inert';
}

function getAtomInfo(name) {
    return ROLE_DESC[name] || { role: 'inert', desc: 'Inert element: ' + name };
}

/**
 * Detect if a list node is a continuation frame (tagged with k-*).
 * Returns the tag string or null.
 */
function getContinuationTag(node) {
    if (node.kind === 'list' && node.list_items && node.list_items.length > 0) {
        const first = node.list_items[0];
        if (first.kind === 'atom' && first.value && first.value.startsWith('k-')) {
            return first.value;
        }
    }
    return null;
}


export class TreeRenderer {
    constructor(container, onNodeSelect) {
        this.container = container;
        this.onNodeSelect = onNodeSelect; // callback(nodeInfo)
        this.selectedEl = null;
        this.onBranchSwap = null; // callback(node, frameIndex) for k-if swaps
    }

    /** Clear the tree display */
    clear() {
        this.container.innerHTML = '';
        this.selectedEl = null;
        // Show watermark
        const wm = document.getElementById('tree-watermark');
        if (wm) wm.style.display = '';
    }

    /** Render a single term tree (for step mode) */
    render(termNode) {
        this.container.innerHTML = '';
        if (!termNode || termNode === 'null') return;

        // Hide watermark
        const wm = document.getElementById('tree-watermark');
        if (wm) wm.style.display = 'none';

        this.container.appendChild(this._buildNode(termNode, 0));
    }

    /** Render multiple result trees (for run mode) */
    showResults(results) {
        this.container.innerHTML = '';
        if (!results || results.length === 0) return;

        const wm = document.getElementById('tree-watermark');
        if (wm) wm.style.display = 'none';

        const info = document.getElementById('tree-info');
        if (info) info.textContent = results.length + ' result' + (results.length !== 1 ? 's' : '');

        results.forEach((r, i) => {
            const wrapper = document.createElement('div');
            wrapper.className = 'tn-result-group';

            // Collapsible header
            const header = document.createElement('div');
            header.className = 'tn-result-header';
            const arrow = document.createElement('span');
            arrow.className = 'tn-result-arrow';
            arrow.textContent = '\u25B6';
            const label = document.createElement('span');
            label.textContent = r.display;

            header.appendChild(arrow);
            header.appendChild(label);

            // Tree body (hidden by default)
            const body = document.createElement('div');
            body.className = 'tn-result-body';
            body.style.display = 'none';
            if (r.tree) body.appendChild(this._buildNode(r.tree, 0));

            header.addEventListener('click', () => {
                const open = body.style.display !== 'none';
                body.style.display = open ? 'none' : 'block';
                arrow.classList.toggle('open', !open);
            });

            wrapper.appendChild(header);
            wrapper.appendChild(body);
            this.container.appendChild(wrapper);
        });
    }

    // ── Private: node builders ──

    _buildNode(node, depth) {
        if (!node) return document.createTextNode('nil');

        // Check for continuation frame
        const contTag = getContinuationTag(node);
        if (contTag) return this._buildContinuationFrame(node, contTag, depth);

        switch (node.kind) {
            case 'atom': return this._buildAtom(node);
            case 'int': return this._buildInt(node);
            case 'list': return this._buildList(node, depth);
            case 'pair': return this._buildPair(node, depth);
            case 'app': return this._buildApp(node, depth);
            default: return this._buildTruncated(node);
        }
    }

    _buildAtom(node) {
        const el = document.createElement('div');
        el.className = 'tn';
        const row = document.createElement('div');
        row.className = 'tn-row';

        const arrow = document.createElement('span');
        arrow.className = 'tn-arrow leaf';
        arrow.textContent = '\u25B6';

        const pill = document.createElement('span');
        pill.className = 'tn-pill ' + atomPillClass(node.value);
        pill.textContent = node.value;
        pill.addEventListener('click', (e) => {
            e.stopPropagation();
            this._select(pill, {
                kind: 'atom',
                value: node.value,
                ...getAtomInfo(node.value)
            });
        });

        row.appendChild(arrow);
        row.appendChild(pill);
        el.appendChild(row);
        return el;
    }

    _buildInt(node) {
        const el = document.createElement('div');
        el.className = 'tn';
        const row = document.createElement('div');
        row.className = 'tn-row';

        const arrow = document.createElement('span');
        arrow.className = 'tn-arrow leaf';
        arrow.textContent = '\u25B6';

        const pill = document.createElement('span');
        pill.className = 'tn-pill tn-pill-int';
        pill.textContent = node.value;
        pill.title = 'Integer: ' + node.int_value + ' (Q-layers around \u22a4)';
        pill.addEventListener('click', (e) => {
            e.stopPropagation();
            this._select(pill, {
                kind: 'int',
                value: node.value,
                role: 'integer',
                desc: node.int_value + ' encoded as Q^' + node.int_value + '(\u22a4)'
            });
        });

        row.appendChild(arrow);
        row.appendChild(pill);
        el.appendChild(row);
        return el;
    }

    _buildApp(node, depth) {
        const el = document.createElement('div');
        el.className = 'tn';

        const row = document.createElement('div');
        row.className = 'tn-row';

        const toggle = document.createElement('button');
        toggle.className = 'tn-toggle';
        const arrow = document.createElement('span');
        arrow.className = 'tn-arrow open';
        arrow.textContent = '\u25B6';
        toggle.appendChild(arrow);

        const label = document.createElement('span');
        label.className = 'tn-struct tn-struct-app';
        label.textContent = 'app';
        label.addEventListener('click', (e) => {
            e.stopPropagation();
            this._select(label, {
                kind: 'app',
                value: 'application',
                role: 'application',
                desc: 'Function application (fun \u00B7 arg)'
            });
        });

        // Show compact form for simple apps: fun(arg)
        const compact = this._compactApp(node);
        if (compact) {
            const compactLabel = document.createElement('span');
            compactLabel.className = 'tn-struct';
            compactLabel.style.color = 'var(--text-dim)';
            compactLabel.style.fontSize = '10px';
            compactLabel.textContent = ' ' + compact;
            row.appendChild(toggle);
            row.appendChild(label);
            row.appendChild(compactLabel);
        } else {
            row.appendChild(toggle);
            row.appendChild(label);
        }

        el.appendChild(row);

        // Children
        const children = document.createElement('div');
        children.className = 'tn-children';

        if (node.children && node.children.length === 2) {
            const funWrap = document.createElement('div');
            const funLabel = document.createElement('span');
            funLabel.className = 'tn-field-label';
            funLabel.textContent = 'fun';
            funWrap.appendChild(funLabel);
            funWrap.appendChild(this._buildNode(node.children[0], depth + 1));
            children.appendChild(funWrap);

            const argWrap = document.createElement('div');
            const argLabel = document.createElement('span');
            argLabel.className = 'tn-field-label';
            argLabel.textContent = 'arg';
            argWrap.appendChild(argLabel);
            argWrap.appendChild(this._buildNode(node.children[1], depth + 1));
            children.appendChild(argWrap);
        }

        el.appendChild(children);

        // Auto-collapse deep apps
        if (depth > 4) {
            children.classList.add('collapsed');
            arrow.classList.remove('open');
        }

        toggle.addEventListener('click', (e) => {
            e.stopPropagation();
            const open = !children.classList.contains('collapsed');
            children.classList.toggle('collapsed', open);
            arrow.classList.toggle('open', !open);
        });

        return el;
    }

    _buildList(node, depth) {
        const el = document.createElement('div');
        el.className = 'tn';
        const items = node.list_items || [];

        const row = document.createElement('div');
        row.className = 'tn-row';

        const toggle = document.createElement('button');
        toggle.className = 'tn-toggle';
        const arrow = document.createElement('span');
        arrow.className = 'tn-arrow open';
        arrow.textContent = '\u25B6';
        toggle.appendChild(arrow);

        const label = document.createElement('span');
        label.className = 'tn-struct tn-struct-list';
        label.textContent = 'list';
        label.addEventListener('click', (e) => {
            e.stopPropagation();
            this._select(label, {
                kind: 'list',
                value: items.length + ' elements',
                role: 'list',
                desc: 'Proper list with ' + items.length + ' elements'
            });
        });

        const count = document.createElement('span');
        count.className = 'tn-count';
        count.textContent = '[' + items.length + ']';

        row.appendChild(toggle);
        row.appendChild(label);
        row.appendChild(count);
        el.appendChild(row);

        const children = document.createElement('div');
        children.className = 'tn-children';

        items.forEach((item, i) => {
            const wrap = document.createElement('div');
            const idx = document.createElement('span');
            idx.className = 'tn-field-label';
            idx.textContent = i;
            wrap.appendChild(idx);
            wrap.appendChild(this._buildNode(item, depth + 1));
            children.appendChild(wrap);
        });

        el.appendChild(children);

        // Auto-collapse
        if (depth > 2 && items.length > 5) {
            children.classList.add('collapsed');
            arrow.classList.remove('open');
        }

        toggle.addEventListener('click', (e) => {
            e.stopPropagation();
            const open = !children.classList.contains('collapsed');
            children.classList.toggle('collapsed', open);
            arrow.classList.toggle('open', !open);
        });

        return el;
    }

    _buildPair(node, depth) {
        const el = document.createElement('div');
        el.className = 'tn';

        const row = document.createElement('div');
        row.className = 'tn-row';

        const toggle = document.createElement('button');
        toggle.className = 'tn-toggle';
        const arrow = document.createElement('span');
        arrow.className = 'tn-arrow open';
        arrow.textContent = '\u25B6';
        toggle.appendChild(arrow);

        const label = document.createElement('span');
        label.className = 'tn-struct tn-struct-pair';
        label.textContent = 'pair';
        label.addEventListener('click', (e) => {
            e.stopPropagation();
            this._select(label, {
                kind: 'pair',
                value: 'dotted pair',
                role: 'pair',
                desc: 'Cons cell (car . cdr)'
            });
        });

        row.appendChild(toggle);
        row.appendChild(label);
        el.appendChild(row);

        const children = document.createElement('div');
        children.className = 'tn-children';

        if (node.children && node.children.length === 2) {
            const carWrap = document.createElement('div');
            const carLabel = document.createElement('span');
            carLabel.className = 'tn-field-label';
            carLabel.textContent = 'car';
            carWrap.appendChild(carLabel);
            carWrap.appendChild(this._buildNode(node.children[0], depth + 1));
            children.appendChild(carWrap);

            const cdrWrap = document.createElement('div');
            const cdrLabel = document.createElement('span');
            cdrLabel.className = 'tn-field-label';
            cdrLabel.textContent = 'cdr';
            cdrWrap.appendChild(cdrLabel);
            cdrWrap.appendChild(this._buildNode(node.children[1], depth + 1));
            children.appendChild(cdrWrap);
        }

        el.appendChild(children);

        if (depth > 4) {
            children.classList.add('collapsed');
            arrow.classList.remove('open');
        }

        toggle.addEventListener('click', (e) => {
            e.stopPropagation();
            const open = !children.classList.contains('collapsed');
            children.classList.toggle('collapsed', open);
            arrow.classList.toggle('open', !open);
        });

        return el;
    }

    _buildContinuationFrame(node, tag, depth) {
        const el = document.createElement('div');
        el.className = 'tn';

        const items = node.list_items || [];

        // Frame card
        const frame = document.createElement('div');
        frame.className = 'tn-cont-frame';
        if (depth === 0) frame.classList.add('tn-current-frame');

        const tagEl = document.createElement('span');
        tagEl.className = 'tn-cont-tag';
        tagEl.textContent = tag;
        frame.appendChild(tagEl);

        // Brief field summary
        if (items.length > 1) {
            const summary = document.createElement('span');
            summary.className = 'tn-struct';
            summary.style.fontSize = '10px';
            summary.textContent = '(' + (items.length - 1) + ' field' + (items.length > 2 ? 's' : '') + ')';
            frame.appendChild(summary);
        }

        frame.addEventListener('click', (e) => {
            e.stopPropagation();
            this._select(frame, {
                kind: 'continuation',
                value: tag,
                role: 'continuation frame',
                desc: 'Continuation frame: ' + tag + ' (' + (items.length - 1) + ' fields)',
                depth: depth
            });
        });

        el.appendChild(frame);

        // k-if branch swap interaction
        if (tag === 'k-if' && items.length >= 3) {
            const branches = document.createElement('div');
            branches.className = 'tn-branches';

            const thenBranch = document.createElement('span');
            thenBranch.className = 'tn-branch tn-branch-then';
            thenBranch.textContent = 'then';
            thenBranch.title = 'Then branch';

            const swapBtn = document.createElement('button');
            swapBtn.className = 'tn-swap-btn';
            swapBtn.textContent = '\u21C4';
            swapBtn.title = 'Swap branches';
            swapBtn.addEventListener('click', (e) => {
                e.stopPropagation();
                // Animate
                thenBranch.classList.add('tn-swap-anim');
                elseBranch.classList.add('tn-swap-anim');
                setTimeout(() => {
                    thenBranch.classList.remove('tn-swap-anim');
                    elseBranch.classList.remove('tn-swap-anim');
                }, 400);

                if (this.onBranchSwap) {
                    this.onBranchSwap(node, depth);
                }
            });

            const elseBranch = document.createElement('span');
            elseBranch.className = 'tn-branch tn-branch-else';
            elseBranch.textContent = 'else';
            elseBranch.title = 'Else branch';

            branches.appendChild(thenBranch);
            branches.appendChild(swapBtn);
            branches.appendChild(elseBranch);
            el.appendChild(branches);
        }

        // Expandable children (frame fields beyond tag)
        if (items.length > 1) {
            const children = document.createElement('div');
            children.className = 'tn-children';

            for (let i = 1; i < items.length; i++) {
                const wrap = document.createElement('div');

                // Check if this child is another continuation frame (chain)
                const childTag = getContinuationTag(items[i]);
                if (childTag) {
                    const chain = document.createElement('div');
                    chain.className = 'tn-cont-chain';
                    chain.textContent = '';
                    wrap.appendChild(chain);
                }

                wrap.appendChild(this._buildNode(items[i], depth + 1));
                children.appendChild(wrap);
            }

            el.appendChild(children);
        }

        return el;
    }

    _buildTruncated(node) {
        const el = document.createElement('div');
        el.className = 'tn';
        const row = document.createElement('div');
        row.className = 'tn-row';
        const span = document.createElement('span');
        span.className = 'tn-struct';
        span.textContent = node.value || '\u2026';
        row.appendChild(span);
        el.appendChild(row);
        return el;
    }

    /** Compact display for simple apps like Atom(Atom) */
    _compactApp(node) {
        if (!node.children || node.children.length !== 2) return null;
        const fun = node.children[0];
        const arg = node.children[1];
        if (fun.kind === 'atom' && (arg.kind === 'atom' || arg.kind === 'int')) {
            return fun.value + '(' + (arg.value || '') + ')';
        }
        return null;
    }

    /** Select a node and show it in the inspector */
    _select(el, info) {
        if (this.selectedEl) this.selectedEl.classList.remove('selected');
        el.classList.add('selected');
        this.selectedEl = el;
        if (this.onNodeSelect) this.onNodeSelect(info);
    }
}
