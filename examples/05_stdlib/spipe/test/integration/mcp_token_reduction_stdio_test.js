import assert from "node:assert/strict";
import { spawn, spawnSync } from "node:child_process";
import { constants, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

const moduleRoot = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
const server = join(moduleRoot, "mcp/server.js");
const target = `A-${"9".repeat(26)}`;
const secureNoFollowAvailable = typeof constants.O_NOFOLLOW === "number";
const MAX_DOC_BYTES = 256 * 1024;

// Wire contract: handler errors are reported with a null id, so replies are
// matched to requests by order (the transport processes lines synchronously).
test("packaged stdio server keeps MCP responses bounded and refuses traversal", { skip: !secureNoFollowAvailable }, () => {
  const root = mkdtempSync(join(tmpdir(), "spipe-mcp-stdio-bounds-"));
  try {
    const inventoryPath = join(root, "inventory.json");
    const artifacts = [{ uid: target, canonical_path: "doc/target.md" }];
    const edges = [];
    for (let i = 0; i < 5; i++) {
      const source = `A-${String(i).repeat(26)}`;
      artifacts.push({ uid: source, canonical_path: `src/mod${i}.spl` });
      edges.push({ uid: `E-${String(i).repeat(26)}`, from_uid: source, to_uid: target, edge_type: "uses", provenance: { source_location: null } });
    }
    writeFileSync(inventoryPath, JSON.stringify({
      snapshot: { snapshot_uid: `spks1-${"1".repeat(64)}` },
      artifacts,
      graph: { graph_root: `sha256:${"2".repeat(64)}`, edges }
    }));

    const largestDoc = "doc/00_llm_process/skill_command/skills/pipe/impl/stitch/skill.md";
    const messages = [
      { jsonrpc: "2.0", id: 1, method: "tools/call", params: { name: "spipe_read_doc", arguments: { path: "../AGENTS.md" } } },
      { jsonrpc: "2.0", id: 2, method: "tools/call", params: { name: "spipe_read_doc", arguments: { path: "/etc/passwd" } } },
      { jsonrpc: "2.0", id: 3, method: "tools/call", params: { name: "spipe_read_doc", arguments: { path: "package.json" } } },
      { jsonrpc: "2.0", id: 4, method: "tools/call", params: { name: "spipe_read_doc", arguments: { path: largestDoc } } },
      { jsonrpc: "2.0", id: 5, method: "tools/call", params: { name: "spipe_folder_reverse_references", arguments: { inventory_path: inventoryPath, target_uid: target, folder_path: "", limit: 2 } } },
      { jsonrpc: "2.0", id: 6, method: "tools/call", params: { name: "spipe_experts", arguments: {} } }
    ];
    const run = spawnSync(process.execPath, [server], {
      input: `${messages.map(JSON.stringify).join("\n")}\n`, encoding: "utf8", timeout: 10_000
    });
    assert.equal(run.status, 0, run.stderr);
    const replies = run.stdout.trim().split("\n").map(JSON.parse);
    assert.equal(replies.length, messages.length);

    // Traversal and allowlist refusals arrive as null-id errors, never content.
    assert.match(replies[0].error.message, /relative path inside the SPipe module/);
    assert.match(replies[1].error.message, /relative path inside the SPipe module/);
    assert.match(replies[2].error.message, /outside the SPipe documentation allowlist/);

    // The largest whitelisted document in the tree stays under the 256 KiB cap.
    const docText = replies[3].result.content[0].text;
    assert.ok(Buffer.byteLength(docText, "utf8") <= MAX_DOC_BYTES, "whitelisted doc response exceeds the size cap");
    assert.match(docText, /stitch|impl/i);

    // Reverse references paginate: limit=2 returns at most 2 edges plus a cursor.
    const page1 = JSON.parse(replies[4].result.content[0].text);
    assert.ok(page1.items.length <= 2);
    assert.equal(page1.complete, false);
    assert.equal(typeof page1.next_cursor, "string");
    assert.ok(Buffer.byteLength(replies[4].result.content[0].text, "utf8") < 16 * 1024, "pagination response is not compact");

    // Expert listing stays compact.
    const experts = replies[5].result.content[0].text;
    assert.ok(Buffer.byteLength(experts, "utf8") < 4096, "expert listing is not compact");
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("packaged stdio server walks authenticated cursors and rejects tampering", { skip: !secureNoFollowAvailable }, async () => {
  const root = mkdtempSync(join(tmpdir(), "spipe-mcp-stdio-cursor-"));
  try {
    const inventoryPath = join(root, "inventory.json");
    const artifacts = [{ uid: target, canonical_path: "doc/target.md" }];
    const edges = [];
    for (let i = 0; i < 5; i++) {
      const source = `A-${String(i).repeat(26)}`;
      artifacts.push({ uid: source, canonical_path: `src/mod${i}.spl` });
      edges.push({ uid: `E-${String(i).repeat(26)}`, from_uid: source, to_uid: target, edge_type: "uses", provenance: { source_location: null } });
    }
    writeFileSync(inventoryPath, JSON.stringify({
      snapshot: { snapshot_uid: `spks1-${"1".repeat(64)}` },
      artifacts,
      graph: { graph_root: `sha256:${"2".repeat(64)}`, edges }
    }));

    // Cursor keys are per server process, so the walk must stay inside one
    // live server: send each request only after the previous reply arrives.
    const child = spawn(process.execPath, [server], { stdio: ["pipe", "pipe", "inherit"] });
    try {
      let pending = Buffer.alloc(0);
      const replies = [];
      child.stdout.on("data", (chunk) => {
        pending += chunk;
        let newline;
        while ((newline = pending.indexOf("\n")) >= 0) {
          const line = pending.slice(0, newline).trim();
          pending = pending.slice(newline + 1);
          if (line) replies.push(JSON.parse(line));
        }
      });
      const nextReply = () => new Promise((resolvePromise, reject) => {
        const timer = setTimeout(() => reject(new Error("timed out waiting for MCP reply")), 10_000);
        const poll = () => {
          if (replies.length) { clearTimeout(timer); resolvePromise(replies.shift()); }
          else setImmediate(poll);
        };
        poll();
      });
      const call = async (id, arguments_) => {
        child.stdin.write(JSON.stringify({ jsonrpc: "2.0", id, method: "tools/call", params: { name: "spipe_folder_reverse_references", arguments: arguments_ } }) + "\n");
        return nextReply();
      };

      const query = { inventory_path: inventoryPath, target_uid: target, folder_path: "" };
      const page1 = JSON.parse((await call(1, { ...query, limit: 2 })).result.content[0].text);
      assert.equal(page1.items.length, 2);
      assert.equal(page1.complete, false);

      const page2 = JSON.parse((await call(2, { ...query, limit: 2, cursor: page1.next_cursor })).result.content[0].text);
      assert.equal(page2.items.length, 2);
      assert.equal(page2.complete, false);

      const tampered = page1.next_cursor.slice(0, -4) + "AAAA";
      assert.match((await call(3, { ...query, limit: 2, cursor: tampered })).error.message, /cursor authentication failed/);
      assert.match((await call(4, { ...query, limit: 1001 })).error.message, /between 1 and 1000/);
    } finally {
      child.kill();
    }
  } finally { rmSync(root, { recursive: true, force: true }); }
});
