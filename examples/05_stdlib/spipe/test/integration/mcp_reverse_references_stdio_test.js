import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

const moduleRoot = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
const server = join(moduleRoot, "mcp/server.js");
const target = `A-${"9".repeat(26)}`;
const source = `A-${"1".repeat(26)}`;

test("packaged stdio server exposes and runs folder reverse-reference queries", () => {
  const root = mkdtempSync(join(tmpdir(), "spipe-mcp-stdio-reverse-"));
  try {
    const inventoryPath = join(root, "inventory.json");
    writeFileSync(inventoryPath, JSON.stringify({
      snapshot: { snapshot_uid: `spks1-${"1".repeat(64)}` },
      artifacts: [
        { uid: target, canonical_path: "doc/target.md" },
        { uid: source, canonical_path: "src/main.spl" }
      ],
      graph: { graph_root: `sha256:${"2".repeat(64)}`, edges: [
        { uid: `E-${"3".repeat(26)}`, from_uid: source, to_uid: target, edge_type: "uses", provenance: { source_location: null } }
      ] }
    }));
    const messages = [
      { jsonrpc: "2.0", id: 1, method: "tools/list" },
      { jsonrpc: "2.0", id: 2, method: "tools/call", params: { name: "spipe_folder_reverse_references", arguments: { inventory_path: inventoryPath, target_uid: target, folder_path: "src" } } }
    ];
    const run = spawnSync(process.execPath, [server], {
      input: `${messages.map(JSON.stringify).join("\n")}\n`, encoding: "utf8", timeout: 10_000
    });
    assert.equal(run.status, 0, run.stderr);
    const replies = run.stdout.trim().split("\n").map(JSON.parse);
    assert.ok(replies[0].result.tools.some(({ name }) => name === "spipe_folder_reverse_references"));
    const page = JSON.parse(replies[1].result.content[0].text);
    assert.deepEqual(page.items.map(({ source_path }) => source_path), ["src/main.spl"]);
    assert.equal(page.complete, true);
  } finally { rmSync(root, { recursive: true, force: true }); }
});
