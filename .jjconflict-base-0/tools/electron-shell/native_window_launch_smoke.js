#!/usr/bin/env node

const { resolveNativeWindowTarget } = require('./native_window_launch');

function assert(condition, message) {
    if (!condition) throw new Error(message);
}

function decodeDataUrl(url) {
    const marker = 'data:text/html;charset=utf-8,';
    if (!String(url).startsWith(marker)) return '';
    return decodeURIComponent(url.slice(marker.length));
}

function main() {
    const fallback = resolveNativeWindowTarget({
        rawUrl: '/wm/native_window?app_id=examples%2Fhello_taskbar&surface_id=host-surface-1&window_id=host-window-1',
        title: 'Hello Taskbar',
        mainWindowUrl: 'file:///tmp/simple/index.html'
    });
    assert(fallback.mode === 'fallback', `expected fallback mode, got ${fallback.mode}`);
    assert(fallback.reason === 'native_window_path_without_http_origin', `unexpected fallback reason: ${fallback.reason}`);
    const fallbackHtml = decodeDataUrl(fallback.url);
    assert(fallbackHtml.includes('examples/hello_taskbar'), 'fallback HTML did not preserve app id');
    assert(fallbackHtml.includes('Hello Taskbar'), 'fallback HTML did not preserve title');
    assert(!fallback.url.includes('file:///wm/native_window'), 'fallback emitted broken file URL');

    const configured = resolveNativeWindowTarget({
        rawUrl: '/wm/native_window?app_id=examples%2Fhello_taskbar',
        localHttpPort: '8123'
    });
    assert(configured.mode === 'configured_origin', `expected configured origin mode, got ${configured.mode}`);
    assert(configured.url === 'http://127.0.0.1:8123/wm/native_window?app_id=examples%2Fhello_taskbar', `unexpected configured URL: ${configured.url}`);

    const hosted = resolveNativeWindowTarget({
        rawUrl: '/wm/native_window?app_id=examples%2Fhello_taskbar',
        mainWindowUrl: 'http://localhost:9000/index.html'
    });
    assert(hosted.mode === 'main_window_origin', `expected main window origin mode, got ${hosted.mode}`);
    assert(hosted.url === 'http://localhost:9000/wm/native_window?app_id=examples%2Fhello_taskbar', `unexpected main-window URL: ${hosted.url}`);

    const absolute = resolveNativeWindowTarget({
        rawUrl: 'data:text/html,<title>Smoke</title>'
    });
    assert(absolute.mode === 'absolute', `expected absolute mode, got ${absolute.mode}`);
    assert(absolute.url === 'data:text/html,<title>Smoke</title>', 'absolute URL was modified');

    console.log('Electron native-window launch smoke passed');
}

main();
