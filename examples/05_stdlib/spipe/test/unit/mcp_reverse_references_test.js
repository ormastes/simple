import assert from "node:assert/strict";
import { mkdtempSync, renameSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";

import { createRouter } from "../../mcp/protocol/router.js";
import { CompiledInventoryReverseReferenceService } from "../../mcp/protocol/reverse_references.js";

const snapshot = `spks1-${"1".repeat(64)}`;
const graphRoot = `sha256:${"2".repeat(64)}`;
const target = `A-${"9".repeat(26)}`;
const sourceOne = `A-${"1".repeat(26)}`;
const sourceTwo = `A-${"2".repeat(26)}`;

function inventory(edges = [edge(2, sourceTwo), edge(1, sourceOne)]) {
  return {
    snapshot: { snapshot_uid: snapshot },
    artifacts: [
      { uid: target, canonical_path: "doc/target.md" },
      { uid: sourceOne, canonical_path: "doc/a/one.md" },
      { uid: sourceTwo, canonical_path: "doc/a/two.md" }
    ],
    graph: { graph_root: graphRoot, edges }
  };
}

function edge(number, source) {
  return { uid: `E-${String(number).repeat(26)}`, from_uid: source, to_uid: target, edge_type: "links_to", provenance: { source_location: null } };
}

function call(route, args, id = 1) {
  return route({ jsonrpc: "2.0", id, method: "tools/call", params: { name: "spipe_folder_reverse_references", arguments: args } });
}

test("MCP schema publishes exact bounded reverse-reference inputs", () => {
  const route = createRouter({ moduleRoot: "." });
  const listed = route({ jsonrpc: "2.0", id: 1, method: "tools/list" });
  const tool = listed.result.tools.find(({ name }) => name === "spipe_folder_reverse_references");
  assert.ok(tool);
  assert.deepEqual(tool.inputSchema.required, ["inventory_path", "target_uid"]);
  assert.equal(tool.inputSchema.additionalProperties, false);
  assert.equal(tool.inputSchema.properties.limit.maximum, 1000);
  assert.equal(tool.inputSchema.properties.max_work_units.maximum, 500000);
});

test("MCP query paginates deterministically and binds its cursor", () => {
  const root = mkdtempSync(join(tmpdir(), "spipe-mcp-reverse-"));
  try {
    const path = join(root, "inventory.json");
    writeFileSync(path, JSON.stringify(inventory()));
    const service = new CompiledInventoryReverseReferenceService({ cursor_key: Buffer.alloc(32, 4) });
    const route = createRouter({ moduleRoot: root, reverseReferenceService: service });
    const args = { inventory_path: path, target_uid: target, folder_path: "doc/a", limit: 1, max_work_units: 1 };
    const first = JSON.parse(call(route, args).result.content[0].text);
    assert.deepEqual(first.items.map(({ source_path }) => source_path), ["doc/a/one.md"]);
    assert.equal(first.reason, "limit");
    const second = JSON.parse(call(route, { ...args, cursor: first.next_cursor }, 2).result.content[0].text);
    assert.deepEqual(second.items.map(({ source_path }) => source_path), ["doc/a/two.md"]);
    assert.equal(second.complete, true);
    assert.throws(() => call(route, { ...args, folder_path: "doc", cursor: first.next_cursor }), (error) => error.code === "SPK704");
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("MCP query rejects malformed, aliased, and unknown inputs", () => {
  const root = mkdtempSync(join(tmpdir(), "spipe-mcp-reverse-"));
  try {
    const path = join(root, "inventory.json");
    writeFileSync(path, JSON.stringify(inventory()));
    const route = createRouter({ moduleRoot: root });
    assert.throws(() => call(route, { inventory_path: path, target_uid: target, extra: true }), /unknown reverse-reference argument/);
    assert.throws(() => call(route, { inventory_path: path, target_uid: target, limit: 0 }), /between 1 and 1000/);
    writeFileSync(join(root, "bad.json"), "not-json");
    assert.throws(() => call(route, { inventory_path: join(root, "bad.json"), target_uid: target }), /valid JSON/);
    symlinkSync(path, join(root, "inventory-link.json"));
    assert.throws(() => call(route, { inventory_path: join(root, "inventory-link.json"), target_uid: target }), /not a symbolic link/);
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("MCP query invalidates a replaced compiled inventory", () => {
  const root = mkdtempSync(join(tmpdir(), "spipe-mcp-reverse-"));
  try {
    const path = join(root, "inventory.json");
    writeFileSync(path, JSON.stringify(inventory([edge(1, sourceOne)])));
    const service = new CompiledInventoryReverseReferenceService({ cursor_key: Buffer.alloc(32, 5) });
    const route = createRouter({ moduleRoot: root, reverseReferenceService: service });
    const args = { inventory_path: path, target_uid: target, folder_path: "doc/a" };
    const first = JSON.parse(call(route, args).result.content[0].text);
    assert.deepEqual(first.items.map(({ source_path }) => source_path), ["doc/a/one.md"]);

    const replacement = inventory([edge(2, sourceTwo)]);
    replacement.graph.graph_root = `sha256:${"3".repeat(64)}`;
    const nextPath = join(root, "replacement.json");
    writeFileSync(nextPath, JSON.stringify(replacement));
    renameSync(nextPath, path);
    const second = JSON.parse(call(route, args, 2).result.content[0].text);
    assert.deepEqual(second.items.map(({ source_path }) => source_path), ["doc/a/two.md"]);
    assert.equal(second.graph_root, replacement.graph.graph_root);
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("MCP inventory read stays on one descriptor across an adversarial pathname swap", () => {
  const root = mkdtempSync(join(tmpdir(), "spipe-mcp-reverse-"));
  try {
    const path = join(root, "inventory.json");
    const heldPath = join(root, "inventory-opened.json");
    const outsidePath = join(root, "outside.json");
    writeFileSync(path, JSON.stringify(inventory([edge(1, sourceOne)])));
    writeFileSync(outsidePath, JSON.stringify(inventory([edge(2, sourceTwo)])));
    let swapped = false;
    const service = new CompiledInventoryReverseReferenceService({
      cursor_key: Buffer.alloc(32, 6),
      opened_file_observer() {
        if (swapped) return;
        swapped = true;
        renameSync(path, heldPath);
        symlinkSync(outsidePath, path);
      }
    });
    const args = { inventory_path: path, target_uid: target, folder_path: "doc/a" };
    const page = JSON.parse(call(createRouter({ moduleRoot: root, reverseReferenceService: service }), args).result.content[0].text);
    assert.deepEqual(page.items.map(({ source_path }) => source_path), ["doc/a/one.md"]);
    assert.throws(() => service.query(args), /not a symbolic link/);
  } finally { rmSync(root, { recursive: true, force: true }); }
});
