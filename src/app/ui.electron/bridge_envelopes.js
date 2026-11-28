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
    const css = msg.css || '';
    return `
        window.__SIMPLE_WEB_RENDER_ENVELOPE__ = ${JSON.stringify(metadata)};
        (function() {
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
            var activeEl = document.activeElement;
            var activeId = (activeEl && activeEl.id) ? activeEl.id : '';
            var activeSelStart = null;
            var activeSelEnd = null;
            if (activeEl && (activeEl.tagName === 'INPUT' || activeEl.tagName === 'TEXTAREA')) {
                try {
                    if (typeof activeEl.selectionStart === 'number') activeSelStart = activeEl.selectionStart;
                    if (typeof activeEl.selectionEnd === 'number') activeSelEnd = activeEl.selectionEnd;
                } catch (_e) {}
            }
            var winScrollX = typeof window.scrollX === 'number' ? window.scrollX : 0;
            var winScrollY = typeof window.scrollY === 'number' ? window.scrollY : 0;
            var appScrollTop = el.scrollTop || 0;
            var scrollById = {};
            if (el.querySelectorAll) {
                var scrollNodes = el.querySelectorAll('[id]');
                for (var si = 0; si < scrollNodes.length; si++) {
                    var sn = scrollNodes[si];
                    if (sn && sn.id && sn.scrollTop) {
                        scrollById[sn.id] = sn.scrollTop;
                    }
                }
            }
            el.innerHTML = ${JSON.stringify(bodyHtml)};
            if (appScrollTop) {
                el.scrollTop = appScrollTop;
            }
            var scrollIds = Object.keys(scrollById);
            for (var sj = 0; sj < scrollIds.length; sj++) {
                var sid = scrollIds[sj];
                var restoredScroll = document.getElementById(sid);
                if (restoredScroll) {
                    restoredScroll.scrollTop = scrollById[sid];
                }
            }
            if (typeof window.scrollTo === 'function' && (winScrollX || winScrollY)) {
                window.scrollTo(winScrollX, winScrollY);
            }
            if (activeId) {
                var restoredFocus = document.getElementById(activeId);
                if (restoredFocus && typeof restoredFocus.focus === 'function') {
                    restoredFocus.focus();
                    if ((restoredFocus.tagName === 'INPUT' || restoredFocus.tagName === 'TEXTAREA') &&
                        activeSelStart !== null && typeof restoredFocus.setSelectionRange === 'function') {
                        try {
                            restoredFocus.setSelectionRange(activeSelStart, activeSelEnd !== null ? activeSelEnd : activeSelStart);
                        } catch (_e2) {}
                    }
                }
            }
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
