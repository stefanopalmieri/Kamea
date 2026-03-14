// Ψ∗ WASM Worker — runs computation off the UI thread

let psi = null;

async function initWasm() {
    // Dynamic import works in workers with module type
    const wasm = await import('./pkg/psi_web.js');
    await wasm.default();
    psi = new wasm.PsiDebugger();
    postMessage({ type: 'ready' });
}

self.onmessage = async function(e) {
    const { type, id, payload } = e.data;

    if (type === 'init') {
        try {
            await initWasm();
        } catch (err) {
            postMessage({ type: 'error', id, error: 'WASM init failed: ' + err.message });
        }
        return;
    }

    if (!psi) {
        postMessage({ type: 'error', id, error: 'WASM not loaded' });
        return;
    }

    try {
        switch (type) {
            case 'run': {
                const result = psi.run(payload.source);
                const stats = psi.stats();
                postMessage({ type: 'run-result', id, result, stats });
                break;
            }
            case 'table': {
                const table = psi.table();
                postMessage({ type: 'table-result', id, table });
                break;
            }
            case 'reset': {
                psi.reset();
                postMessage({ type: 'reset-result', id });
                break;
            }
            case 'stats': {
                const stats = psi.stats();
                postMessage({ type: 'stats-result', id, stats });
                break;
            }
            default:
                postMessage({ type: 'error', id, error: 'unknown message type: ' + type });
        }
    } catch (err) {
        postMessage({ type: 'error', id, error: err.message || String(err) });
    }
};
