import assert from "node:assert/strict";
import { existsSync, lstatSync, mkdirSync, mkdtempSync, readdirSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { spawn } from "node:child_process";
import test from "node:test";
import { pathToFileURL } from "node:url";

import { mkdirDurable } from "../../src/storage/directory_fsync.js";

const JOURNAL_URL = pathToFileURL(join(import.meta.dirname, "../../src/storage/authority_publication_journal.js")).href;

test("mkdirDurable fsyncs every newly created ancestor and its parent entry", () => {
  const root = mkdtempSync(join(tmpdir(), "spkc-mkdir-durable-"));
  try {
    const synced = [];
    const target = join(root, "worktrees", "w1", "authority-publications");
    mkdirDurable(target, { fsyncDirectory: (p) => synced.push(p) });
    for (const dir of [join(root, "worktrees"), join(root, "worktrees", "w1"), target]) {
      assert.ok(synced.includes(dir), `directory ${dir} must be fsynced`);
      assert.ok(synced.includes(dirname(dir)), `parent entry ${dirname(dir)} must be fsynced`);
    }
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("mkdirDurable accepts a directory created by a concurrent winner and still fsyncs it", () => {
  const root = mkdtempSync(join(tmpdir(), "spkc-mkdir-durable-"));
  try {
    const synced = [];
    const target = join(root, "a", "b");
    const racing = (p) => { mkdirSync(p); throw Object.assign(new Error("EEXIST"), { code: "EEXIST" }); };
    mkdirDurable(target, { mkdirSync: racing, fsyncDirectory: (p) => synced.push(p) });
    assert.ok(lstatSync(target).isDirectory());
    assert.ok(synced.includes(target) && synced.includes(join(root, "a")));
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("mkdirDurable rejects a symlink/non-directory ancestor", () => {
  const root = mkdtempSync(join(tmpdir(), "spkc-mkdir-durable-"));
  try {
    const racing = (p) => { throw Object.assign(new Error("EEXIST"), { code: "EEXIST" }); };
    assert.throws(() => mkdirDurable(join(root, "x"), { mkdirSync: racing, fsyncDirectory: () => {} }));
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("independent processes racing first-use journal construction on an absent ledger all succeed", async () => {
  const PROCS = 6, ROUNDS = 5;
  for (let round = 0; round < ROUNDS; round += 1) {
    const base = mkdtempSync(join(tmpdir(), "spkc-journal-race-"));
    const cacheRoot = join(base, "shared", "spipe", "cache");
    const gate = join(base, "go");
    const child = `
      import { existsSync, writeFileSync } from "node:fs";
      const { AuthorityPublicationJournalV1 } = await import(${JSON.stringify(JOURNAL_URL)});
      writeFileSync(${JSON.stringify(gate)} + ".ready-" + process.pid, "");
      while (!existsSync(${JSON.stringify(gate)})) { await new Promise((r) => setTimeout(r, 1)); }
      try { new AuthorityPublicationJournalV1({ cacheRoot: ${JSON.stringify(cacheRoot)}, worktreeUid: "w1" }); process.exit(0); }
      catch (e) { console.error(e?.code ?? "", e?.message); process.exit(3); }`;
    try {
      const procs = [];
      for (let i = 0; i < PROCS; i += 1) {
        const p = spawn(process.execPath, ["--input-type=module", "-e", child], { stdio: ["ignore", "ignore", "pipe"] });
        let err = "";
        p.stderr.on("data", (d) => { err += d; });
        procs.push(new Promise((r) => p.on("exit", (code) => r({ code, err }))));
      }
      const deadline = Date.now() + 30000;
      while (readdirSync(base).filter((n) => n.startsWith("go.ready-")).length < PROCS) {
        assert.ok(Date.now() < deadline, "children never became ready");
        await new Promise((r) => setTimeout(r, 5));
      }
      mkdirSync(gate);
      const results = await Promise.all(procs);
      for (const r of results) assert.equal(r.code, 0, `child failed: ${r.err}`);
      assert.ok(existsSync(join(cacheRoot, "worktrees", "w1", "authority-publications", "records")));
    } finally { rmSync(base, { recursive: true, force: true }); }
  }
});
