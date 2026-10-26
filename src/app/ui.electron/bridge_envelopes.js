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

// macOS `hiddenInset` windows underlap content beneath the native traffic-light
// cluster; WM/MDI mode hides the native titlebar entirely. Reserve a 28px top
// strip in that mode so content never jams against (or under) the native
// controls, and make the strip a drag region so plain renders stay movable.
function darwinHiddenInsetMode() {
    return process.platform === 'darwin' && !process.env.SIMPLE_ELECTRON_TITLE;
}

const DARWIN_TOP_INSET_PX = 28;

function darwinTopInsetScript() {
    if (!darwinHiddenInsetMode()) return '';
    return `
        (function() {
            var strip = document.getElementById('simple-electron-top-inset');
            if (!strip) {
                strip = document.createElement('div');
                strip.id = 'simple-electron-top-inset';
                strip.style.cssText = 'position:fixed;top:0;left:0;right:0;height:${DARWIN_TOP_INSET_PX}px;z-index:99998;-webkit-app-region:drag;background:transparent;';
                document.body.appendChild(strip);
            }
            document.body.style.paddingTop = '${DARWIN_TOP_INSET_PX}px';
        })();
    `;
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
        ${darwinTopInsetScript()}
        window.dispatchEvent(new CustomEvent('simple-render', {
            detail: { html: ${JSON.stringify(bodyHtml)}, envelope: window.__SIMPLE_WEB_RENDER_ENVELOPE__ }
        }));
    `;
}

module.exports = {
    commonInputEnvelope,
    darwinHiddenInsetMode,
    darwinTopInsetScript,
    renderEnvelopeMetadata,
    renderEnvelopeScript
};
