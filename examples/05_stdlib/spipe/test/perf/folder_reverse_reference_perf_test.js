#!/usr/bin/env node
import assert from "node:assert/strict";
import { performance } from "node:perf_hooks";

import { FolderReverseReferenceIndex } from "../../src/graph/index.js";

const EDGE_COUNT = Number(process.env.SPIPE_REVERSE_REFERENCE_PERF_EDGES ?? 50_000);
const TARGET_EDGE_COUNT = Number(process.env.SPIPE_REVERSE_REFERENCE_PERF_TARGET_EDGES ?? 250);
const SAMPLES = Number(process.env.SPIPE_REVERSE_REFERENCE_PERF_SAMPLES ?? 12);
const MODE = process.env.SPIPE_REVERSE_REFERENCE_PERF_MODE ?? "cli-target";
const target = `A-${"9".repeat(26)}`;

function uid(prefix, number) {
  return `${prefix}-${number.toString(36).padStart(26, "0")}`;
}

function fixture() {
  const artifacts = [{ uid: target, canonical_path: "doc/target.md" }];
  const edges = [];
  for (let index = 0; index < EDGE_COUNT; index += 1) {
    const source = uid("A", index + 1);
    artifacts.push({ uid: source, canonical_path: `src/group-${index % 64}/file-${index}.spl` });
    edges.push({
      uid: uid("E", index + 1), from_uid: source,
      to_uid: index < TARGET_EDGE_COUNT ? target : uid("A", EDGE_COUNT + index + 1),
      edge_type: "links_to", provenance: { source_location: null }
    });
  }
  return { artifacts, edges };
}

function percentile(values, fraction) {
  const ordered = [...values].sort((left, right) => left - right);
  return ordered[Math.ceil(ordered.length * fraction) - 1];
}

const data = fixture();
const samples = [];
let peakRss = process.memoryUsage().rss;
for (let sample = 0; sample < SAMPLES; sample += 1) {
  global.gc?.();
  const start = performance.now();
  const index = new FolderReverseReferenceIndex({
    snapshot_uid: `spks1-${"1".repeat(64)}`, graph_root: `sha256:${"2".repeat(64)}`,
    artifacts: data.artifacts, edges: data.edges, cursor_key: Buffer.alloc(32, 7),
    ...(MODE === "cli-target" ? { indexed_target_uid: target } : {})
  });
  const result = index.query({ target_uid: target, folder_path: "src", limit: TARGET_EDGE_COUNT });
  samples.push(performance.now() - start);
  peakRss = Math.max(peakRss, process.memoryUsage().rss);
  assert.equal(result.items.length, TARGET_EDGE_COUNT);
  assert.equal(result.complete, true);
}

const report = {
  mode: MODE, edge_count: EDGE_COUNT, target_edge_count: TARGET_EDGE_COUNT, samples: SAMPLES,
  p50_ms: Number(percentile(samples, 0.5).toFixed(3)),
  p95_ms: Number(percentile(samples, 0.95).toFixed(3)),
  peak_rss_bytes: peakRss
};
assert.ok(["cli-target", "mcp-lazy"].includes(MODE), `unknown benchmark mode: ${MODE}`);
assert.ok(report.p95_ms <= 650, `reverse-reference P95 ${report.p95_ms} ms exceeds 650 ms`);
assert.ok(report.peak_rss_bytes <= 230 * 1024 * 1024, `reverse-reference RSS ${report.peak_rss_bytes} exceeds 230 MiB`);
console.log(JSON.stringify(report));
