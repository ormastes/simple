#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const args = process.argv.slice(2);

function valueAfter(flag) {
    const index = args.indexOf(flag);
    return index >= 0 ? args[index + 1] : '';
}

const htmlPath = valueAfter('--html');
const ppmPath = valueAfter('--out');
const width = Number(valueAfter('--width') || '160');
const height = Number(valueAfter('--height') || '120');

if (!htmlPath || !ppmPath) {
    console.error('Usage: node tools/electron-shell/playwright_file_to_ppm.js --html <file.html> --out <file.ppm> [--width 160] [--height 120]');
    process.exit(2);
}

const root = path.resolve(__dirname, '..', '..');
const absHtml = path.resolve(root, htmlPath);
const absPpm = path.resolve(root, ppmPath);
const tmpPng = path.join('/tmp', `simple_playwright_${process.pid}.png`);

fs.mkdirSync(path.dirname(absPpm), { recursive: true });

function run(command, commandArgs) {
    const result = spawnSync(command, commandArgs, {
        cwd: root,
        encoding: 'utf8',
        stdio: 'pipe'
    });
    if (result.error) throw result.error;
    if (result.status !== 0) {
        throw new Error(`${command} ${commandArgs.join(' ')} failed\n${result.stdout || ''}${result.stderr || ''}`);
    }
    return result;
}

try {
    run('npx', [
        'playwright', 'screenshot',
        '--browser', 'chromium',
        `--viewport-size=${width},${height}`,
        '--timeout', '30000',
        `file://${absHtml}`,
        tmpPng
    ]);
    run('node', [
        'tools/electron-shell/png_to_ppm.js',
        tmpPng,
        absPpm,
        String(width),
        String(height)
    ]);
    console.log(`wrote ${absPpm}`);
} catch (err) {
    console.error(err.stack || err.message || err);
    process.exit(1);
} finally {
    try {
        fs.unlinkSync(tmpPng);
    } catch {
        // best-effort temp cleanup
    }
}
