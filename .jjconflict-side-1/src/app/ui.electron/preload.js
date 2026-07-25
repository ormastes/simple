const { contextBridge, ipcRenderer } = require('electron');

function sendInput(envelope) {
    ipcRenderer.send('simple-input', envelope);
}

function commonInputEnvelope(eventType, fields = {}) {
    return {
        type: 'input',
        target: 'electron',
        surface_id: fields.surface_id || 'main',
        event_type: eventType,
        target_id: fields.target_id || '',
        key: fields.key || '',
        value: fields.value || '',
        x: Number(fields.x || 0),
        y: Number(fields.y || 0),
        dx: Number(fields.dx || 0),
        dy: Number(fields.dy || 0),
        button: fields.button || ''
    };
}

window.addEventListener('DOMContentLoaded', () => {
    document.addEventListener('keydown', event => {
        const allowed = event.key.length === 1 || [
            'Enter', 'Escape', 'Backspace', 'Tab',
            'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'
        ].includes(event.key);
        if (allowed) {
            sendInput(commonInputEnvelope('key', { key: event.key }));
        }
    });

    document.addEventListener('click', event => {
        const action = event.target && event.target.closest
            ? event.target.closest('[data-action]')
            : null;
        if (action) {
            sendInput(commonInputEnvelope('action', { value: action.getAttribute('data-action') || '' }));
        }
    });
});

contextBridge.exposeInMainWorld('simpleElectron', {
    sendInput,
    envelope() {
        return window.__SIMPLE_WEB_RENDER_ENVELOPE__ || null;
    },
    runtimeVersions() {
        return {
            electron: process.versions.electron || '',
            chrome: process.versions.chrome || ''
        };
    }
});
