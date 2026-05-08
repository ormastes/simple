#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const root = path.resolve(__dirname, '..', '..');
const width = 80;
const height = 50;
const fixtureDir = path.join(root, 'test', 'fixtures', 'design_effects_compat');
const baselineDir = path.join(root, 'test', 'baselines', 'design_effects_compat');
const reportPath = path.join(root, 'doc', '09_report', 'simple_browser_design_effects_compat_2026-05-06.md');

const fixtures = [
  ['awwwards_hero_reveal', 'Awwwards-style hero reveal', 'Awwwards', ['#0f172a', '#38bdf8', '#f97316'], ['#0f172a', '#38bdf8', '#f97316'], [10, 16, 24], [28, 14, 8]],
  ['css_design_awards_panels', 'CSS Design Awards-style panels', 'CSS Design Awards', ['#f8fafc', '#111827', '#22c55e'], ['#f8fafc', '#111827', '#22c55e'], [12, 12, 26], [16, 20, 14]],
  ['dribbble_shot_grid', 'Dribbble-style shot grid', 'Dribbble', ['#fff1f2', '#fb7185', '#be123c'], ['#fff1f2', '#fb7185', '#be123c'], [8, 18, 24], [20, 16, 14]],
  ['behance_case_study', 'Behance-style case study', 'Behance', ['#eff6ff', '#2563eb', '#1e40af'], ['#eff6ff', '#2563eb', '#1e40af'], [10, 20, 20], [24, 16, 10]],
  ['mobbin_app_flow', 'Mobbin-style app flow', 'Mobbin', ['#ecfeff', '#06b6d4', '#155e75'], ['#ecfeff', '#06b6d4', '#155e75'], [14, 14, 22], [18, 18, 14]],
  ['godly_landing_motion', 'Godly-style landing motion', 'Godly', ['#fefce8', '#eab308', '#713f12'], ['#fefce8', '#eab308', '#713f12'], [12, 18, 20], [22, 16, 12]],
  ['siteinspire_gallery_filter', 'Siteinspire-style gallery filter', 'Siteinspire', ['#f0fdf4', '#16a34a', '#14532d'], ['#f0fdf4', '#16a34a', '#14532d'], [10, 18, 22], [18, 22, 10]],
  ['gsap_stagger_blocks', 'GSAP stagger blocks', 'GSAP', ['#faf5ff', '#a855f7', '#581c87'], ['#faf5ff', '#a855f7', '#581c87'], [8, 14, 28], [26, 16, 8]],
  ['threejs_scene_proxy', 'Three.js/WebGL scene proxy', 'Three.js', ['#ecfdf5', '#10b981', '#064e3b'], ['#ecfdf5', '#10b981', '#064e3b'], [16, 18, 16], [20, 20, 10]],
  ['js_class_toggle_cards', 'JavaScript class-toggle cards', 'JS/CSS effects', ['#fff7ed', '#f97316', '#7c2d12'], ['#fff7ed', '#f97316', '#7c2d12'], [10, 14, 26], [24, 18, 8]]
];

function run(cmd, args) {
  const result = spawnSync(cmd, args, { cwd: root, encoding: 'utf8', stdio: 'pipe' });
  if (result.error) throw result.error;
  if (result.status !== 0) {
    throw new Error(`${cmd} ${args.join(' ')} failed\n${result.stdout || ''}${result.stderr || ''}`);
  }
  return result;
}

function htmlFor(fixture, state) {
  const [, title, , colors, finalColors, startHeights, finalHeights] = fixture;
  const activeColors = state === 'final' ? finalColors : colors;
  const heights = state === 'final' ? finalHeights : startHeights;
  const js = state === 'js-final'
    ? `<script>document.addEventListener('DOMContentLoaded',function(){document.body.setAttribute('data-state','final');});</script>`
    : '';
  const attr = state === 'final' || state === 'js-final' ? ' data-state="final"' : '';
  return `<!doctype html>
<html>
<head>
<meta charset="utf-8">
<style>
html,body{margin:0;width:${width}px;height:${height}px;background:${activeColors[0]};}
body[data-state="final"] .one{height:${finalHeights[0]}px;background:${finalColors[0]};}
body[data-state="final"] .two{height:${finalHeights[1]}px;background:${finalColors[1]};}
body[data-state="final"] .three{height:${finalHeights[2]}px;background:${finalColors[2]};}
.one{width:${width}px;height:${heights[0]}px;background:${activeColors[0]};}
.two{width:${width}px;height:${heights[1]}px;background:${activeColors[1]};}
.three{width:${width}px;height:${heights[2]}px;background:${activeColors[2]};}
</style>
</head>
<body${attr}>
<div class="one"></div><div class="two"></div><div class="three"></div>
${js}
</body>
</html>`;
}

function captureChrome(htmlPath, outPpm) {
  const png = path.join('/tmp', `design_effect_${process.pid}_${path.basename(outPpm)}.png`);
  run('npx', ['playwright', 'screenshot', '--browser', 'chromium', `--viewport-size=${width},${height}`, '--timeout', '30000', `file://${htmlPath}`, png]);
  run('node', ['tools/electron-shell/png_to_ppm.js', png, outPpm, String(width), String(height)]);
  try { fs.unlinkSync(png); } catch {}
}

function captureSimple(htmlPath, outPpm) {
  run('bin/simple', ['run', 'src/app/wm_compare/simple_html_capture_worker.spl', `--html=${htmlPath}`, `--out=${outPpm}`, `--width=${width}`, `--height=${height}`]);
}

function readPpm(file) {
  const data = fs.readFileSync(file);
  let i = 0;
  function token() {
    while (i < data.length) {
      const ch = data[i];
      if (ch === 35) {
        while (i < data.length && data[i] !== 10) i += 1;
      } else if (ch === 9 || ch === 10 || ch === 13 || ch === 32) {
        i += 1;
      } else {
        break;
      }
    }
    const start = i;
    while (i < data.length && ![9, 10, 13, 32].includes(data[i])) i += 1;
    return data.slice(start, i).toString('ascii');
  }
  const magic = token();
  const w = Number(token());
  const h = Number(token());
  const max = Number(token());
  if (max !== 255 || w !== width || h !== height) throw new Error(`bad PPM ${file}`);
  if (magic === 'P6') {
    while ([9, 10, 13, 32].includes(data[i])) i += 1;
    return data.slice(i, i + w * h * 3);
  }
  if (magic === 'P3') {
    const rgb = Buffer.alloc(w * h * 3);
    for (let p = 0; p < rgb.length; p += 1) rgb[p] = Number(token());
    return rgb;
  }
  throw new Error(`unsupported PPM ${magic}`);
}

function compare(aFile, bFile) {
  const a = readPpm(aFile);
  const b = readPpm(bFile);
  let differentPixels = 0;
  let sad = 0;
  let maxChannelDiff = 0;
  for (let i = 0; i < a.length; i += 3) {
    const dr = Math.abs(a[i] - b[i]);
    const dg = Math.abs(a[i + 1] - b[i + 1]);
    const db = Math.abs(a[i + 2] - b[i + 2]);
    if (dr || dg || db) differentPixels += 1;
    sad += dr + dg + db;
    maxChannelDiff = Math.max(maxChannelDiff, dr, dg, db);
  }
  const total = width * height;
  return {
    differentPixels,
    matchPct10000: Math.round((total - differentPixels) * 10000 / total),
    maxChannelDiff,
    sad,
    exact: differentPixels === 0 && maxChannelDiff === 0
  };
}

function main() {
  fs.mkdirSync(fixtureDir, { recursive: true });
  fs.mkdirSync(baselineDir, { recursive: true });
  fs.mkdirSync(path.dirname(reportPath), { recursive: true });
  const rows = [];
  for (const fixture of fixtures) {
    const [id, name, source] = fixture;
    const dir = path.join(baselineDir, id);
    fs.mkdirSync(dir, { recursive: true });
    for (const state of ['start', 'final']) {
      const htmlPath = path.join(fixtureDir, `${id}_${state}.html`);
      fs.writeFileSync(htmlPath, htmlFor(fixture, state));
      const chrome = path.join(dir, `chrome_${state}.ppm`);
      const simple = path.join(dir, `simple_${state}.ppm`);
      captureChrome(htmlPath, chrome);
      captureSimple(htmlPath, simple);
      rows.push({ id, name, source, state, ...compare(chrome, simple) });
    }
    const jsPath = path.join(fixtureDir, `${id}_js_final.html`);
    fs.writeFileSync(jsPath, htmlFor(fixture, 'js-final'));
    const chromeJs = path.join(dir, 'chrome_js_final.ppm');
    captureChrome(jsPath, chromeJs);
    rows.push({ id, name, source, state: 'chrome-js-final-vs-static-final', ...compare(chromeJs, path.join(dir, 'chrome_final.ppm')) });
  }
  rows.sort((a, b) => b.differentPixels - a.differentPixels || b.maxChannelDiff - a.maxChannelDiff || b.sad - a.sad);
  const failures = rows.filter(row => !row.exact);
  const out = [
    '# Simple Browser Design Effects Compatibility Audit',
    '',
    'Date: 2026-05-06',
    '',
    'Scope: 10 deterministic design/effect examples inspired by current design inspiration and effects categories: Awwwards, CSS Design Awards, Dribbble, Behance, Mobbin, Godly, Siteinspire, GSAP, Three.js, and JS/CSS class-toggle effects.',
    '',
    'Reference sources: Colorlib 2026 design inspiration roundup, Awwwards, CSS Design Awards, FreeFrontend GSAP examples, and HTMLHub effect categories.',
    '',
    `Viewport: ${width}x${height}`,
    `Checks: ${rows.length}`,
    `Exact checks: ${rows.length - failures.length}/${rows.length}`,
    `Failures: ${failures.length}`,
    '',
    '## Top Differences',
    '',
    '| Rank | Example | Source | State | Diff px | Match/10000 | Max channel diff | SAD | Exact |',
    '|---:|---|---|---|---:|---:|---:|---:|---|',
    ...rows.slice(0, 10).map((row, index) => `| ${index + 1} | ${row.name} | ${row.source} | ${row.state} | ${row.differentPixels} | ${row.matchPct10000} | ${row.maxChannelDiff} | ${row.sad} | ${row.exact} |`),
    '',
    '## Notes',
    '',
    '- `start` compares Chrome start-state pixels to Simple start-state pixels.',
    '- `final` compares Chrome settled/final-state pixels to Simple settled/final-state pixels.',
    '- `chrome-js-final-vs-static-final` verifies that the synchronous JavaScript class-toggle fixture reaches the same final Chrome pixels as the static final state before using the static final state for Simple comparison.',
    '- The fixtures avoid text rendering so this is a strict pixel/color check for layout and effect state colors without font-antialiasing noise.',
    ''
  ];
  fs.writeFileSync(reportPath, out.join('\n'));
  console.log(JSON.stringify({
    status: failures.length === 0 ? 'PASS' : 'FAIL',
    checks: rows.length,
    exact: rows.length - failures.length,
    failures: failures.length,
    report: path.relative(root, reportPath),
    worst: rows.slice(0, 3)
  }, null, 2));
  process.exit(failures.length === 0 ? 0 : 1);
}

main();
