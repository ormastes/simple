const { URL } = require('url');

function escapeHtml(value) {
    return String(value || '')
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#39;');
}

function hasAbsoluteScheme(url) {
    return /^[a-zA-Z][a-zA-Z\d+.-]*:/.test(String(url || ''));
}

function parseHttpOrigin(url) {
    if (!url) return '';
    try {
        const parsed = new URL(url);
        if (parsed.protocol === 'http:' || parsed.protocol === 'https:') {
            return parsed.origin;
        }
    } catch (err) {
        return '';
    }
    return '';
}

function parsePortOrigin(portValue) {
    const port = Number.parseInt(String(portValue || ''), 10);
    if (!Number.isFinite(port) || port <= 0 || port > 65535) return '';
    return `http://127.0.0.1:${port}`;
}

function isNativeWindowPath(url) {
    const value = String(url || '');
    return value.startsWith('/wm/native_window') || value.startsWith('wm/native_window');
}

function queryParam(rawUrl, key) {
    try {
        const parsed = new URL(String(rawUrl || ''), 'https://simple.invalid');
        return parsed.searchParams.get(key) || '';
    } catch (err) {
        return '';
    }
}

function buildFallbackHtml(rawUrl, title) {
    const appId = queryParam(rawUrl, 'app_id');
    const surfaceId = queryParam(rawUrl, 'surface_id');
    const windowId = queryParam(rawUrl, 'window_id');
    const displayTitle = title || appId || windowId || 'Simple App';
    return `<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>${escapeHtml(displayTitle)}</title>
    <style>
        :root {
            color-scheme: dark;
            --bg: #10131a;
            --surface: rgba(27, 31, 42, 0.92);
            --border: rgba(175, 193, 230, 0.22);
            --fg: #edf2ff;
            --muted: #9eabc8;
            --accent: #87b7ff;
        }
        * { box-sizing: border-box; }
        body {
            margin: 0;
            min-height: 100vh;
            padding: 24px;
            font: 14px/1.5 "Manrope", "Inter", -apple-system, BlinkMacSystemFont, sans-serif;
            color: var(--fg);
            background:
                radial-gradient(circle at top, rgba(135, 183, 255, 0.18), transparent 42%),
                linear-gradient(180deg, #0a0d12 0%, var(--bg) 100%);
        }
        main {
            max-width: 680px;
            padding: 24px;
            border: 1px solid var(--border);
            border-radius: 18px;
            background: var(--surface);
            box-shadow: 0 24px 60px rgba(0, 0, 0, 0.38);
        }
        h1 {
            margin: 0 0 8px;
            font-size: 22px;
        }
        p {
            margin: 0 0 16px;
            color: var(--muted);
        }
        dl {
            display: grid;
            grid-template-columns: max-content 1fr;
            gap: 8px 14px;
            margin: 18px 0 0;
        }
        dt {
            color: var(--accent);
            font-weight: 600;
        }
        dd {
            margin: 0;
            overflow-wrap: anywhere;
        }
    </style>
</head>
<body>
    <main>
        <h1>${escapeHtml(displayTitle)}</h1>
        <p>Electron loaded this host window without a Simple Web HTTP origin, so the shell rendered the local fallback document instead of navigating to a broken file URL.</p>
        <dl>
            <dt>App</dt><dd>${escapeHtml(appId || '(unknown)')}</dd>
            <dt>Surface</dt><dd>${escapeHtml(surfaceId || '(unknown)')}</dd>
            <dt>Window</dt><dd>${escapeHtml(windowId || '(unknown)')}</dd>
            <dt>Requested URL</dt><dd>${escapeHtml(rawUrl || '(empty)')}</dd>
        </dl>
    </main>
</body>
</html>`;
}

function buildFallbackDataUrl(rawUrl, title) {
    return `data:text/html;charset=utf-8,${encodeURIComponent(buildFallbackHtml(rawUrl, title))}`;
}

function resolveNativeWindowTarget(options = {}) {
    const rawUrl = String(options.rawUrl || '').trim();
    const title = String(options.title || '');
    if (!rawUrl) {
        return {
            url: buildFallbackDataUrl('', title),
            mode: 'fallback',
            reason: 'empty_url'
        };
    }
    if (hasAbsoluteScheme(rawUrl)) {
        return {
            url: rawUrl,
            mode: 'absolute'
        };
    }

    const mainWindowOrigin = parseHttpOrigin(options.mainWindowUrl);
    if (mainWindowOrigin) {
        return {
            url: new URL(rawUrl, mainWindowOrigin).toString(),
            mode: 'main_window_origin'
        };
    }

    const localHttpOrigin = parsePortOrigin(options.localHttpPort);
    if (localHttpOrigin) {
        return {
            url: new URL(rawUrl, localHttpOrigin).toString(),
            mode: 'configured_origin'
        };
    }

    if (isNativeWindowPath(rawUrl)) {
        return {
            url: buildFallbackDataUrl(rawUrl, title),
            mode: 'fallback',
            reason: 'native_window_path_without_http_origin'
        };
    }

    try {
        return {
            url: new URL(rawUrl, options.mainWindowUrl || 'file:///').toString(),
            mode: 'relative'
        };
    } catch (err) {
        return {
            url: buildFallbackDataUrl(rawUrl, title),
            mode: 'fallback',
            reason: 'unresolvable_relative_url'
        };
    }
}

module.exports = {
    buildFallbackHtml,
    resolveNativeWindowTarget
};
