// Ψ∗ WASM Worker — runs computation off the UI thread

let psi = null;

async function initWasm() {
    const wasm = await import('./pkg/psi_web.js');
    await wasm.default(new URL('./pkg/psi_web_bg.wasm', self.location.href));
    psi = new wasm.PsiDebugger();
    postMessage({ type: 'ready' });
}

self.onmessage = async function (e) {
    const { type, id, payload } = e.data;

    if (type === 'init') {
        try { await initWasm(); }
        catch (err) { postMessage({ type: 'error', id, error: 'WASM init failed: ' + err.message }); }
        return;
    }

    if (!psi) {
        postMessage({ type: 'error', id, error: 'WASM not loaded' });
        return;
    }

    try {
        switch (type) {
            case 'run': {
                let result, stats;
                try {
                    result = psi.run_with_trees(payload.source);
                } catch (runErr) {
                    // If run_with_trees panics (stack overflow, etc.),
                    // the RefCell borrow may be stuck. Recreate the debugger.
                    const wasm = await import('./pkg/psi_web.js');
                    psi = new wasm.PsiDebugger();
                    postMessage({ type: 'result', id, result: JSON.stringify({ error: runErr.message || String(runErr), results: [], io_output: '' }), stats: '{}' });
                    break;
                }
                stats = psi.stats();
                postMessage({ type: 'result', id, result, stats });
                break;
            }
            case 'table': {
                const table = psi.table();
                postMessage({ type: 'result', id, table });
                break;
            }
            case 'start_stepping': {
                psi.reset();
                const display = psi.start_stepping(payload.expr);
                const term = psi.current_term();
                const stats = psi.stats();
                postMessage({ type: 'result', id, display, term, stats });
                break;
            }
            case 'step': {
                const info = psi.step();
                const term = psi.current_term();
                const stats = psi.stats();
                postMessage({ type: 'result', id, info, term, stats });
                break;
            }
            case 'run_to_completion': {
                const result = psi.run_to_completion();
                const term = psi.current_term();
                const stats = psi.stats();
                postMessage({ type: 'result', id, result, term, stats });
                break;
            }
            case 'eval_trace': {
                const trace = psi.eval_trace();
                postMessage({ type: 'result', id, trace });
                break;
            }
            case 'reset': {
                psi.reset();
                postMessage({ type: 'result', id });
                break;
            }
            case 'stats': {
                const stats = psi.stats();
                postMessage({ type: 'result', id, stats });
                break;
            }
            default:
                postMessage({ type: 'error', id, error: 'unknown: ' + type });
        }
    } catch (err) {
        postMessage({ type: 'error', id, error: err.message || String(err) });
    }
};
