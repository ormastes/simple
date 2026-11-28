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

function handleFormValueEvent(event) {
    const el = event.target && event.target.closest
        ? event.target.closest('input[id], textarea[id], select[id]')
        : null;
    if (!el || !el.id) {
        return;
    }
    if (el.tagName === 'SELECT') {
        sendInput(commonInputEnvelope('action', { value: 'select_' + el.id + '_' + el.selectedIndex }));
        return;
    }
    sendInput(commonInputEnvelope('input', { target_id: el.id, value: el.value }));
}

function registerPreloadListeners(doc) {
    doc.addEventListener('keydown', event => {
        const isFormControl = !!(event.target && event.target.matches && event.target.matches('input, textarea, select'));
        if (isFormControl) {
            if (event.key === 'Escape' || event.key === 'Tab') {
                sendInput(commonInputEnvelope('key', { key: event.key }));
            }
            return;
        }
        const allowed = event.key.length === 1 || [
            'Enter', 'Escape', 'Backspace', 'Tab',
            'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'
        ].includes(event.key);
        if (allowed) {
            sendInput(commonInputEnvelope('key', { key: event.key }));
        }
    });

    doc.addEventListener('click', event => {
        const target = event.target;
        const action = target && target.closest
            ? target.closest('[data-action]')
            : null;
        if (action) {
            sendInput(commonInputEnvelope('action', { value: action.getAttribute('data-action') || '' }));
            return;
        }
        const listItem = target && target.closest
            ? target.closest('.list-item[data-index]')
            : null;
        if (listItem) {
            const list = listItem.closest('.widget-list[id]');
            const idx = listItem.getAttribute('data-index') || '';
            if (list && list.id && idx !== '') {
                sendInput(commonInputEnvelope('action', { value: 'select_' + list.id + '_' + idx }));
            }
        }
    });

    doc.addEventListener('input', handleFormValueEvent);
    doc.addEventListener('change', handleFormValueEvent);

    doc.addEventListener('focusin', event => {
        const el = event.target && event.target.closest
            ? event.target.closest('input[id], textarea[id], select[id], button[id], [data-action][id]')
            : null;
        if (el && el.id) {
            sendInput(commonInputEnvelope('focus', { target_id: el.id }));
        }
    });
}

window.addEventListener('DOMContentLoaded', () => {
    registerPreloadListeners(document);
});

contextBridge.exposeInMainWorld('simpleElectron', {
    sendInput,
    envelope() {
        return window.__SIMPLE_WEB_RENDER_ENVELOPE__ || null;
    }
});
