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
    const bodyHtml = msg.body_html || msg.html || '';
    const rootAttrs = (msg.root_attrs || '').trim();
    const css = msg.css || '';
    const renderProof = {
        ...metadata,
        body_html_length: bodyHtml.length,
        css_length: css.length,
        root_attrs_length: rootAttrs.length
    };
    return `
        window.__SIMPLE_WEB_RENDER_ENVELOPE__ = ${JSON.stringify(renderProof)};
        (function() {
            var root = document.documentElement;
            var rootAttrs = ${JSON.stringify(rootAttrs)};
            if (root && rootAttrs) {
                var probe = document.createElement('div');
                probe.innerHTML = '<span ' + rootAttrs + '></span>';
                var source = probe.firstElementChild;
                if (source) {
                    var attrIndex = 0;
                    while (attrIndex < source.attributes.length) {
                        var attr = source.attributes[attrIndex];
                        root.setAttribute(attr.name, attr.value);
                        attrIndex = attrIndex + 1;
                    }
                }
            }
            var cssText = ${JSON.stringify(css)};
            if (cssText) {
                var styleEl = document.getElementById('simple-server-css');
                if (!styleEl) {
                    styleEl = document.createElement('style');
                    styleEl.id = 'simple-server-css';
                    document.head.appendChild(styleEl);
                }
                if (styleEl.textContent !== cssText) {
                    styleEl.textContent = cssText;
                }
            }
            var el = document.getElementById('app');
            if (!el) {
                document.body.innerHTML = '<div id="app"></div>';
                el = document.getElementById('app');
            }
            el.innerHTML = ${JSON.stringify(bodyHtml)};
        })();
        window.dispatchEvent(new CustomEvent('simple-render', {
            detail: { html: ${JSON.stringify(bodyHtml)}, envelope: window.__SIMPLE_WEB_RENDER_ENVELOPE__ }
        }));
    `;
}

module.exports = {
    commonInputEnvelope,
    renderEnvelopeMetadata,
    renderEnvelopeScript
};
