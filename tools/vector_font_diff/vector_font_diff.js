#!/usr/bin/env node
// Compare chrome.json vs simple.json glyph ink metrics; print summary + verdict.
//
// Tolerances (per glyph, on ink metrics of the same TTF at the same px size):
//   bbox w/h : |delta| <= max(2px, 5% of chrome value)  — AA edge + rounding
//   ink      : |delta| <= 10% of chrome ink pixel count
//   density  : |delta| <= 80 permille
const fs = require("fs");
const [chromePath, simplePath, ttf] = process.argv.slice(2);
const chrome = JSON.parse(fs.readFileSync(chromePath, "utf8"));
const simple = JSON.parse(fs.readFileSync(simplePath, "utf8"));

const simpleByCp = new Map(simple.glyphs.map((g) => [g.cp, g]));
let compared = 0, findings = 0;
const lines = [];
for (const cg of chrome.glyphs) {
  const sg = simpleByCp.get(cg.cp);
  if (!sg) { lines.push(`MISSING cp=${cg.cp} on simple side`); findings += 1; continue; }
  compared += 1;
  const checks = [
    ["w", Math.abs(cg.w - sg.w), Math.max(2, cg.w * 0.05)],
    ["h", Math.abs(cg.h - sg.h), Math.max(2, cg.h * 0.05)],
    ["ink", Math.abs(cg.ink - sg.ink), Math.max(20, cg.ink * 0.10)],
    // density is unstable for tiny glyphs (e.g. "."): a 1px bbox delta moves
    // it by ~100 permille, so only check it where the bbox has real area.
    ...(cg.w * cg.h >= 400
      ? [["density", Math.abs(cg.density_permille - sg.density_permille), 80]]
      : []),
  ];
  for (const [name, delta, tol] of checks) {
    if (delta > tol) {
      lines.push(`FINDING cp=${cg.cp} ${name}: chrome vs simple delta=${delta.toFixed(1)} tol=${tol.toFixed(1)}`);
      findings += 1;
    }
  }
}
console.log(`chrome_version=${chrome.chrome_version}`);
console.log(`ttf=${ttf}`);
console.log(`size_px=${chrome.size}`);
console.log(`glyphs_compared=${compared}`);
console.log(`findings=${findings}`);
for (const l of lines) console.log(l);
if (compared === 0) {
  console.log("vector-font-diff verdict: ERROR — nothing was compared");
  process.exit(4);
}
if (findings > 0) {
  console.log(`vector-font-diff verdict: FAIL — ${findings} finding(s) over ${compared} glyph(s)`);
  process.exit(1);
}
console.log(`vector-font-diff verdict: PASS — ${compared} glyph(s) compared, 0 findings`);
