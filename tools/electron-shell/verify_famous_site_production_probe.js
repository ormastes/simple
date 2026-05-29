#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const sampleArg = process.argv.find((arg) => arg.startsWith("--sample="));
const sample = sampleArg ? sampleArg.slice("--sample=".length) : "site_0_google";
const maxDifferentPixels = sample === "site_0_google" ? 2717 : 6000;
const dir = path.join(root, "test", "baselines", "famous_site_corpus", sample);
const reportPath = path.join(dir, "report.production.sdn");

function matchText(text, regex, fallback = "") {
  const match = text.match(regex);
  return match ? match[1] : fallback;
}

function parseBool(text, regex) {
  return matchText(text, regex, "false") === "true";
}

function parseIntField(text, regex) {
  return Number.parseInt(matchText(text, regex, "0"), 10);
}

function parsePpm(filePath) {
  if (!fs.existsSync(filePath)) return null;
  const bytes = fs.readFileSync(filePath);
  const headerEnd = bytes.indexOf(Buffer.from("\n255\n"));
  if (headerEnd < 0) return null;
  const header = bytes.slice(0, headerEnd).toString("ascii").trim().split(/\s+/);
  const width = Number.parseInt(header[1], 10);
  const height = Number.parseInt(header[2], 10);
  const dataStart = headerEnd + 5;
  if (header[0] === "P6") {
    return { width, height, data: bytes.slice(dataStart, dataStart + width * height * 3) };
  }
  if (header[0] === "P3") {
    const values = bytes.slice(dataStart).toString("ascii").trim().split(/\s+/).map((v) => Number.parseInt(v, 10));
    return { width, height, data: Uint8Array.from(values.slice(0, width * height * 3)) };
  }
  return null;
}

function differentPixelsFromPpm(aPath, bPath) {
  const a = parsePpm(aPath);
  const b = parsePpm(bPath);
  if (!a || !b || a.width !== b.width || a.height !== b.height) return null;
  let different = 0;
  for (let i = 0; i + 2 < a.data.length && i + 2 < b.data.length; i += 3) {
    if (a.data[i] !== b.data[i] || a.data[i + 1] !== b.data[i + 1] || a.data[i + 2] !== b.data[i + 2]) {
      different += 1;
    }
  }
  return different;
}

const failures = [];
let result = {
  status: "FAIL",
  sample,
  report: path.relative(root, reportPath),
  rendererMode: "",
  exact: false,
  accepted: false,
  divergent: false,
  differentPixels: 0,
  maxDifferentPixels,
  computedDifferentPixels: null,
  reportFresh: false,
  failures
};

if (!fs.existsSync(reportPath)) {
  failures.push("missing production report; run site_corpus_compat.spl with --production-renderer first");
} else {
  const text = fs.readFileSync(reportPath, "utf8");
  const chromeRel = matchText(text, /chrome_ppm:\s*"([^"]+)"/);
  const simpleRel = matchText(text, /simple_ppm:\s*"([^"]+)"/);
  const chromePath = path.join(root, chromeRel);
  const simplePath = path.join(root, simpleRel);
  result.rendererMode = matchText(text, /renderer_mode:\s*"([^"]+)"/);
  result.exact = parseBool(text, /exact:\s*(true|false)/);
  result.accepted = parseBool(text, /accepted:\s*(true|false)/);
  result.differentPixels = parseIntField(text, /different_pixels:\s*([0-9]+)/);
  result.computedDifferentPixels = differentPixelsFromPpm(chromePath, simplePath);
  result.divergent = !result.exact && !result.accepted;
  result.reportFresh = result.computedDifferentPixels === result.differentPixels;
  if (result.rendererMode !== "production") failures.push("report is not renderer_mode production");
  if (!simpleRel.endsWith("/simple.production.ppm")) failures.push("simple_ppm does not use production artifact path");
  if (!result.divergent) failures.push("production probe is not divergent");
  if (!result.reportFresh) failures.push("production report is stale or PPM parse failed");
  if (result.differentPixels <= 1000 || result.differentPixels >= 6000) failures.push("production divergence is outside bounded evidence range");
  if (result.differentPixels > maxDifferentPixels) failures.push("production probe regressed above current focused baseline");
}

result.status = failures.length === 0 ? "PASS" : "FAIL";
console.log(JSON.stringify(result, null, 2));
process.exit(result.status === "PASS" ? 0 : 1);
