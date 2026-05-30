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

function renderEnvelopeMetadata(msg) {
    return {
        target: msg.target || 'electron',
        surface_id: msg.surface_id || 'main',
        width: Number(msg.width || 0),
        height: Number(msg.height || 0)
    };
}

function renderEnvelopeScript(msg) {
    const metadata = renderEnvelopeMetadata(msg);
    return `
        window.__SIMPLE_WEB_RENDER_ENVELOPE__ = ${JSON.stringify(metadata)};
        (function() {
            var el = document.getElementById('app');
            if (!el) {
                document.body.innerHTML = '<div id="app"></div>';
                el = document.getElementById('app');
            }
            el.innerHTML = ${JSON.stringify(msg.html || '')};
        })();
        window.dispatchEvent(new CustomEvent('simple-render', {
            detail: { html: ${JSON.stringify(msg.html || '')}, envelope: window.__SIMPLE_WEB_RENDER_ENVELOPE__ }
        }));
    `;
}

module.exports = {
    commonInputEnvelope,
    renderEnvelopeMetadata,
    renderEnvelopeScript
};
