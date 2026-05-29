/**
 * Bundle the CodeMirror-based webview editor into a single IIFE file.
 * Output: out/webview/mathEditor.js
 */
import * as esbuild from 'esbuild';
import * as path from 'path';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(__dirname, '..');

await esbuild.build({
    entryPoints: [path.join(root, 'src', 'math', 'webview', 'mathEditorWebview.ts')],
    bundle: true,
    format: 'iife',
    globalName: 'MathEditorWebview',
    outfile: path.join(root, 'out', 'webview', 'mathEditor.js'),
    platform: 'browser',
    target: 'es2020',
    sourcemap: true,
    minify: false,
    // Don't externalize anything — bundle everything for the webview
    external: [],
});

console.log('[build-webview] out/webview/mathEditor.js built');
