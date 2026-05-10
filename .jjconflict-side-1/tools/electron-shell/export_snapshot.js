#!/usr/bin/env node
// Electron UI Snapshot Exporter
//
// Captures the first Electron render payload from `bin/simple ui electron`
// and writes a standalone HTML artifact for Stitch analysis.
//
// Usage:
//   node tools/electron-shell/export_snapshot.js --entry examples/ui/demo_menubar_statusbar.ui.sdn
//   node tools/electron-shell/export_snapshot.js --entry examples/ui/demo_kitchen_sink.ui.sdn --png build/ui_snapshots/kitchen_sink.png
//
// Notes:
// - The snapshot reuses the existing Electron UI render path
//   (`generate_css` + `render_html_tree`) and does not generate a custom theme.
// - If Electron IPC render cannot start in the current branch, the tool
//   falls back to tools/electron-shell/export_snapshot.spl
//   (`generate_html_page`) to keep output on the shared HTML/CSS path.
// - The output HTML file is self-contained and suitable for Stitch ingestion.

const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');

const repoRoot = path.resolve(__dirname, '..', '..');
const defaultSimpleBin = path.join(repoRoot, 'bin', 'simple');
const electronAppEntry = path.join(repoRoot, 'src', 'app', 'ui.electron', 'app.spl');
const defaultTimeoutMs = 20000;
const defaultPngTimeoutMs = 30000;
const isWin = process.platform === 'win32';
const electronBinName = isWin ? 'electron.cmd' : 'electron';

function compactLog(text, maxLines = 30, maxChars = 4000) {
    if (!text) return '';
    let out = text;
    if (out.length > maxChars) {
        out = out.slice(0, maxChars);
    }
    const lines = out.split('\n');
    if (lines.length > maxLines) {
        out = lines.slice(0, maxLines).join('\n');
        out += '\n... (truncated)';
    }
    return out;
}

function printHelp() {
    console.log([
        'Export Electron HTML snapshot from Simple UI render payload.',
        '',
        'Usage:',
        '  node tools/electron-shell/export_snapshot.js --entry <file.ui.sdn> [options]',
        '',
        'Options:',
        '  --entry <path>         Input .ui.sdn file (required).',
        '  --out <path>           Output HTML path (default: build/ui_snapshots/<entry>.electron.snapshot.html).',
        '  --png <path>           Also capture PNG using tools/electron-shell/screenshot.js.',
        '  --width <n>            PNG width (default: 1360).',
        '  --height <n>           PNG height (default: 840).',
        '  --simple-bin <path>    Path to Simple binary (default: bin/simple in repo root).',
        '  --timeout-ms <n>       Timeout waiting for first render (default: 20000).',
        '  --no-fallback          Disable fallback exporter (export_snapshot.spl).',
        '  -h, --help             Show help.',
        '',
        'Example:',
        '  node tools/electron-shell/export_snapshot.js --entry examples/ui/demo_menubar_statusbar.ui.sdn --png build/ui_snapshots/demo_menubar_statusbar.png'
    ].join('\n'));
}

function parseArgs(argv) {
    const args = {
        entry: '',
        out: '',
        png: '',
        width: 1360,
        height: 840,
        simpleBin: defaultSimpleBin,
        timeoutMs: defaultTimeoutMs,
        noFallback: false
    };

    for (let i = 0; i < argv.length; i++) {
        const token = argv[i];
        if (token === '-h' || token === '--help') {
            args.help = true;
            continue;
        }
        if (token === '--entry' && i + 1 < argv.length) {
            args.entry = argv[++i];
            continue;
        }
        if (token === '--out' && i + 1 < argv.length) {
            args.out = argv[++i];
            continue;
        }
        if (token === '--png' && i + 1 < argv.length) {
            args.png = argv[++i];
            continue;
        }
        if (token === '--width' && i + 1 < argv.length) {
            args.width = parseInt(argv[++i], 10);
            continue;
        }
        if (token === '--height' && i + 1 < argv.length) {
            args.height = parseInt(argv[++i], 10);
            continue;
        }
        if (token === '--simple-bin' && i + 1 < argv.length) {
            args.simpleBin = argv[++i];
            continue;
        }
        if (token === '--timeout-ms' && i + 1 < argv.length) {
            args.timeoutMs = parseInt(argv[++i], 10);
            continue;
        }
        if (token === '--no-fallback') {
            args.noFallback = true;
            continue;
        }
        if (!token.startsWith('-') && !args.entry) {
            args.entry = token;
            continue;
        }
        throw new Error(`Unknown or incomplete argument: ${token}`);
    }
    return args;
}

function ensureDirFor(filePath) {
    const dir = path.dirname(filePath);
    fs.mkdirSync(dir, { recursive: true });
}

function buildDefaultHtmlOut(entryPath) {
    const base = path.basename(entryPath).replace(/\.ui\.sdn$/i, '');
    return path.join(repoRoot, 'build', 'ui_snapshots', `${base}.electron.snapshot.html`);
}

function normalizeHtmlDocument(html) {
    if (!html || typeof html !== 'string') {
        return '<!DOCTYPE html><html><head><meta charset="utf-8"></head><body></body></html>';
    }
    const trimmed = html.trim();
    if (trimmed.startsWith('<!DOCTYPE html>')) {
        return html;
    }
    if (trimmed.startsWith('<html') || trimmed.startsWith('<HTML')) {
        return `<!DOCTYPE html>\n${html}`;
    }
    return `<!DOCTYPE html>
<html lang="en">
<head><meta charset="utf-8"></head>
<body>${html}</body>
</html>`;
}

function captureFirstRenderHtml(options) {
    return new Promise((resolve, reject) => {
        const entryAbs = path.resolve(repoRoot, options.entry);
        const simpleBinAbs = path.resolve(repoRoot, options.simpleBin);

        if (!fs.existsSync(entryAbs)) {
            reject(new Error(`Entry file not found: ${entryAbs}`));
            return;
        }
        if (!fs.existsSync(simpleBinAbs)) {
            reject(new Error(`Simple binary not found: ${simpleBinAbs}`));
            return;
        }

        const child = spawn(simpleBinAbs, ['run', electronAppEntry, entryAbs], {
            cwd: repoRoot,
            env: {
                ...process.env,
                SIMPLE_UI_BACKEND: 'electron',
                SIMPLE_HOME: repoRoot
            },
            stdio: ['ignore', 'pipe', 'pipe']
        });

        let lineBuffer = '';
        let finished = false;
        let stderrBuf = '';

        const finish = (err, html) => {
            if (finished) return;
            finished = true;
            clearTimeout(timeoutId);
            if (!child.killed) {
                child.kill('SIGTERM');
                setTimeout(() => {
                    if (!child.killed) child.kill('SIGKILL');
                }, 400);
            }
            if (err) {
                reject(err);
                return;
            }
            resolve(html);
        };

        const timeoutId = setTimeout(() => {
            const detailText = compactLog(stderrBuf);
            const detail = detailText.length > 0 ? `\nstderr:\n${detailText}` : '';
            finish(new Error(`Timed out waiting for first render after ${options.timeoutMs}ms.${detail}`));
        }, options.timeoutMs);

        child.stdout.on('data', (chunk) => {
            lineBuffer += chunk.toString();
            const lines = lineBuffer.split('\n');
            lineBuffer = lines.pop() || '';
            for (const rawLine of lines) {
                const line = rawLine.trim();
                if (!line) continue;
                let msg;
                try {
                    msg = JSON.parse(line);
                } catch (_err) {
                    continue;
                }
                if (msg && msg.type === 'render' && typeof msg.html === 'string' && msg.html.length > 0) {
                    finish(null, msg.html);
                    return;
                }
            }
        });

        child.stderr.on('data', (chunk) => {
            stderrBuf += chunk.toString();
        });

        child.on('error', (err) => {
            finish(new Error(`Failed to launch Simple process: ${err.message}`));
        });

        child.on('close', (code) => {
            if (!finished) {
                const detailText = compactLog(stderrBuf);
                const detail = detailText.length > 0 ? `\nstderr:\n${detailText}` : '';
                finish(new Error(`Simple process exited before first render (code=${code}).${detail}`));
            }
        });
    });
}

function exportViaSimpleHtmlGenerator(options, outHtmlPath) {
    return new Promise((resolve, reject) => {
        const simpleBinAbs = path.resolve(repoRoot, options.simpleBin);
        const entryAbs = path.resolve(repoRoot, options.entry);
        const fallbackScript = path.join(repoRoot, 'tools', 'electron-shell', 'export_snapshot.spl');

        if (!fs.existsSync(fallbackScript)) {
            reject(new Error(`Fallback script not found: ${fallbackScript}`));
            return;
        }

        const child = spawn(
            simpleBinAbs,
            ['run', fallbackScript, '--entry', entryAbs, '--out', outHtmlPath, '--port', '3000'],
            {
                cwd: repoRoot,
                env: {
                    ...process.env,
                    SIMPLE_HOME: repoRoot
                },
                stdio: ['ignore', 'pipe', 'pipe']
            }
        );
        let stdoutBuf = '';
        let stderrBuf = '';

        child.stdout.on('data', (chunk) => {
            stdoutBuf += chunk.toString();
        });
        child.stderr.on('data', (chunk) => {
            stderrBuf += chunk.toString();
        });
        child.on('error', (err) => {
            reject(new Error(`Fallback exporter failed to launch: ${err.message}`));
        });
        child.on('close', (code) => {
            if (code === 0 && fs.existsSync(outHtmlPath)) {
                resolve(stdoutBuf.trim());
                return;
            }
            const details = [compactLog(stdoutBuf), compactLog(stderrBuf)].filter(Boolean).join('\n');
            reject(new Error(`Fallback exporter failed (code=${code}).${details ? `\n${details}` : ''}`));
        });
    });
}

function detectElectronBinary() {
    const local = path.join(__dirname, 'node_modules', '.bin', electronBinName);
    if (fs.existsSync(local)) return local;
    return null;
}

function capturePng(htmlPath, pngPath, width, height) {
    return new Promise((resolve, reject) => {
        const electronBin = detectElectronBinary();
        if (!electronBin) {
            reject(new Error('Electron binary not found under tools/electron-shell/node_modules/.bin.'));
            return;
        }
        const screenshotScript = path.join(__dirname, 'screenshot.js');
        const child = spawn(electronBin, [screenshotScript, htmlPath, pngPath, String(width), String(height)], {
            cwd: __dirname,
            stdio: ['ignore', 'pipe', 'pipe']
        });
        let stderrBuf = '';
        let stdoutBuf = '';
        let finished = false;

        const finish = (err, message) => {
            if (finished) return;
            finished = true;
            clearTimeout(timeoutId);
            if (!child.killed) {
                child.kill('SIGTERM');
                setTimeout(() => {
                    if (!child.killed) child.kill('SIGKILL');
                }, 400);
            }
            if (err) {
                reject(err);
                return;
            }
            resolve(message);
        };

        const timeoutId = setTimeout(() => {
            const details = [compactLog(stdoutBuf), compactLog(stderrBuf)].filter(Boolean).join('\n');
            finish(new Error(`Electron screenshot timed out after ${defaultPngTimeoutMs}ms.${details ? `\n${details}` : ''}`));
        }, defaultPngTimeoutMs);

        child.stdout.on('data', (chunk) => {
            stdoutBuf += chunk.toString();
        });
        child.stderr.on('data', (chunk) => {
            stderrBuf += chunk.toString();
        });
        child.on('error', (err) => {
            finish(new Error(`Failed to launch Electron screenshot: ${err.message}`));
        });
        child.on('close', (code) => {
            if (code === 0) {
                finish(null, stdoutBuf.trim());
                return;
            }
            finish(new Error(`Electron screenshot failed (code=${code}).\n${stderrBuf || stdoutBuf}`));
        });
    });
}

async function main() {
    let args;
    try {
        args = parseArgs(process.argv.slice(2));
    } catch (err) {
        console.error(`Error: ${err.message}`);
        console.error('Run with --help for usage.');
        process.exit(1);
        return;
    }

    if (args.help) {
        printHelp();
        return;
    }
    if (!args.entry) {
        printHelp();
        process.exit(1);
        return;
    }
    if (!Number.isFinite(args.width) || args.width <= 0 || !Number.isFinite(args.height) || args.height <= 0) {
        throw new Error('Width/height must be positive integers.');
    }
    if (!Number.isFinite(args.timeoutMs) || args.timeoutMs <= 0) {
        throw new Error('timeout-ms must be a positive integer.');
    }

    const outHtml = path.resolve(repoRoot, args.out || buildDefaultHtmlOut(args.entry));
    ensureDirFor(outHtml);

    let usedFallback = false;
    try {
        const rawHtml = await captureFirstRenderHtml(args);
        const htmlDoc = normalizeHtmlDocument(rawHtml);
        fs.writeFileSync(outHtml, htmlDoc, 'utf8');
        console.log(`HTML snapshot: ${outHtml}`);
    } catch (ipcErr) {
        if (args.noFallback) {
            throw ipcErr;
        }
        console.warn(`Warning: Electron IPC snapshot failed, using fallback HTML generator.\n${ipcErr.message}`);
        await exportViaSimpleHtmlGenerator(args, outHtml);
        usedFallback = true;
        console.log(`HTML snapshot: ${outHtml}`);
    }

    if (usedFallback) {
        console.log('Snapshot source: shared generate_html_page fallback (tools/electron-shell/export_snapshot.spl)');
    } else {
        console.log('Snapshot source: Electron render IPC payload');
    }

    if (args.png) {
        const pngOut = path.resolve(repoRoot, args.png);
        ensureDirFor(pngOut);
        const pngMessage = await capturePng(outHtml, pngOut, args.width, args.height);
        if (pngMessage) {
            console.log(pngMessage);
        } else {
            console.log(`PNG snapshot: ${pngOut}`);
        }
    }
}

main().catch((err) => {
    console.error(`Error: ${err.message}`);
    process.exit(1);
});
