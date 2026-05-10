#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const args = process.argv.slice(2);

function valueAfter(flag) {
    const index = args.indexOf(flag);
    return index >= 0 ? args[index + 1] : '';
}

const root = path.resolve(__dirname, '..', '..');
const fixturesDir = path.join(root, 'test/fixtures/famous_site_corpus');
const baselinesDir = path.join(root, 'test/baselines/famous_site_corpus');
const width = Number(valueAfter('--width') || '160');
const height = Number(valueAfter('--height') || '120');
const limit = Number(valueAfter('--limit') || '0');
const only = valueAfter('--only');

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

const ids = fs.readdirSync(fixturesDir)
    .filter(name => name.endsWith('.html'))
    .map(name => name.slice(0, -'.html'.length))
    .filter(id => !only || id === only)
    .sort();

let written = 0;
for (const id of ids) {
    if (limit > 0 && written >= limit) break;
    const htmlPath = path.join('test/fixtures/famous_site_corpus', `${id}.html`);
    const ppmPath = path.join('test/baselines/famous_site_corpus', id, 'chrome.ppm');
    fs.mkdirSync(path.join(baselinesDir, id), { recursive: true });
    run('node', [
        'tools/electron-shell/playwright_file_to_ppm.js',
        '--html', htmlPath,
        '--out', ppmPath,
        '--width', String(width),
        '--height', String(height)
    ]);
    written += 1;
    console.log(`[capture_famous_site_corpus_chrome] wrote ${id}`);
}

console.log(`[capture_famous_site_corpus_chrome] wrote ${written} Chrome PPM baseline(s)`);
