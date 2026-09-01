import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

const moduleRoot = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
const cli = join(moduleRoot, "cli", "spipe.js");
const snapshot = `spks1-${"1".repeat(64)}`;
const graphRoot = `sha256:${"2".repeat(64)}`;
const target = `A-${"9".repeat(26)}`;
const sourceOne = `A-${"1".repeat(26)}`;
const sourceTwo = `A-${"2".repeat(26)}`;

function edge(number, source) {
  return { uid: `E-${String(number).repeat(26)}`, from_uid: source, to_uid: target, edge_type: "links_to", provenance: { source_location: null } };
}

function invoke(root, ...args) {
  return spawnSync(process.execPath, [cli, "reverse-references", join(root, "inventory.json"), target, "--cursor-key-file", join(root, "cursor.key"), ...args], {
    cwd: root, encoding: "utf8", timeout: 10_000
  });
}

function fixture() {
  const root = mkdtempSync(join(tmpdir(), "spipe-reverse-reference-cli-"));
  writeFileSync(join(root, "cursor.key"), "ab".repeat(32));
  writeFileSync(join(root, "inventory.json"), JSON.stringify({
    snapshot: { snapshot_uid: snapshot },
    artifacts: [
      { uid: target, canonical_path: "doc/target.md" },
      { uid: sourceOne, canonical_path: "doc/a/one.md" },
      { uid: sourceTwo, canonical_path: "doc/a/two.md" }
    ],
    graph: { graph_root: graphRoot, edges: [edge(2, sourceTwo), edge(1, sourceOne)] }
  }));
  return root;
}

test("public CLI queries and paginates one immutable folder view", () => {
  const root = fixture();
  try {
    const firstRun = invoke(root, "--folder", "doc/a", "--limit", "1", "--max-work-units", "1");
    assert.equal(firstRun.status, 0, firstRun.stderr);
    const first = JSON.parse(firstRun.stdout);
    assert.equal(first.complete, false);
    assert.deepEqual(first.items.map((item) => item.source_path), ["doc/a/one.md"]);

    const secondRun = invoke(root, "--folder", "doc/a", "--limit", "1", "--max-work-units", "1", "--cursor", first.next_cursor);
    assert.equal(secondRun.status, 0, secondRun.stderr);
    const second = JSON.parse(secondRun.stdout);
    assert.equal(second.complete, true);
    assert.deepEqual(second.items.map((item) => item.source_path), ["doc/a/two.md"]);
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("public CLI rejects cursor rebinding and missing key authority", () => {
  const root = fixture();
  try {
    const first = JSON.parse(invoke(root, "--folder", "doc/a", "--limit", "1", "--max-work-units", "1").stdout);
    const rebound = invoke(root, "--folder", "doc", "--limit", "1", "--max-work-units", "1", "--cursor", first.next_cursor);
    assert.equal(rebound.status, 2);
    assert.match(rebound.stderr, /folder_path binding mismatch/);
    const missingKey = spawnSync(process.execPath, [cli, "reverse-references", join(root, "inventory.json"), target], { encoding: "utf8" });
    assert.equal(missingKey.status, 2);
    assert.match(missingKey.stderr, /--cursor-key-file is required/);
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("public CLI fails closed on malformed bounded inputs", () => {
  const root = fixture();
  try {
    const invalidLimit = invoke(root, "--limit", "0");
    assert.equal(invalidLimit.status, 2);
    assert.match(invalidLimit.stderr, /--limit must be a positive integer/);

    writeFileSync(join(root, "cursor.key"), "short");
    const invalidKey = invoke(root);
    assert.equal(invalidKey.status, 2);
    assert.match(invalidKey.stderr, /exactly 32 raw bytes/);

    writeFileSync(join(root, "cursor.key"), "ab".repeat(32));
    writeFileSync(join(root, "inventory.json"), "not-json");
    const invalidInventory = invoke(root);
    assert.equal(invalidInventory.status, 2);
    assert.match(invalidInventory.stderr, /valid JSON/);
  } finally { rmSync(root, { recursive: true, force: true }); }
});
