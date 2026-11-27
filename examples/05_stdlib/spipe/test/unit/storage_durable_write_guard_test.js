import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, readdirSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";
import { pathToFileURL } from "node:url";

const SRC = join(import.meta.dirname, "../../src/storage");
const SRC_ROOT = join(import.meta.dirname, "../../src");

// Files that call renameSync but are genuinely not durable publishes (none today).
// Add "relative/path.js": "reason" only with a concrete justification.
const NON_DURABLE_ALLOWLIST = {};

function listJs(dir) {
  const out = [];
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    const p = join(dir, e.name);
    if (e.isDirectory()) out.push(...listJs(p));
    else if (e.name.endsWith(".js")) out.push(p);
  }
  return out;
}

// Guard: every spipe src file that publishes with a renameSync( call must fsync the
// file before the rename and fsync the parent directory after it (#6007 pattern),
// and must not use a Date.now()-only temp name (cross-process collisions).
const renamers = listJs(SRC_ROOT).filter((f) => /renameSync\(/.test(readFileSync(f, "utf8")));
test("guard scans a non-trivial set of renameSync publishers", () => {
  assert.ok(renamers.length >= 6, `expected >=6 renameSync publishers, saw ${renamers.length}`);
});
for (const file of renamers) {
  const rel = file.slice(SRC_ROOT.length + 1).replaceAll("\\", "/");
  if (rel in NON_DURABLE_ALLOWLIST) continue;
  test(`${rel} fsyncs file before rename and directory after`, () => {
    const text = readFileSync(file, "utf8");
    const rename = text.search(/renameSync\(/);
    const fileSync = text.indexOf("fsyncSync(");
    assert.ok(fileSync >= 0 && fileSync < rename, "fsyncSync(file) must precede renameSync(");
    const lastRename = text.lastIndexOf("renameSync(");
    assert.ok(text.indexOf("fsyncDirectory(", rename) > rename && /fsyncDirectory\(/.test(text.slice(lastRename)), "fsyncDirectory must follow renameSync(");
    assert.ok(!/\.tmp-\$\{process\.pid\}-\$\{Date\.now\(\)\}`/.test(text), "temp name must not be pid+Date.now() only");
  });
}

test("concurrent object-store writers of one blob leave one intact object and no temp files", async () => {
  const { ContentAddressedObjectStore, ObjectStore } = await import(pathToFileURL(join(SRC, "object_store.js")).href).then((m) => ({ ContentAddressedObjectStore: m.ContentAddressedObjectStore, ObjectStore: m.ObjectStore }));
  const Store = ContentAddressedObjectStore ?? ObjectStore;
  assert.ok(Store, "object store class export");
  const root = mkdtempSync(join(tmpdir(), "spipe-cas-"));
  try {
    const store = new Store({ root, cacheRoot: root });
    const results = await Promise.all(Array.from({ length: 16 }, async () => store.put("same payload")));
    assert.equal(new Set(results.map((r) => r.hash)).size, 1);
    assert.equal(store.read(results[0].hash).toString(), "same payload");
    const leftovers = [];
    const walk = (d) => { for (const e of readdirSync(d, { withFileTypes: true })) { if (e.isDirectory()) walk(join(d, e.name)); else if (e.name.endsWith(".tmp")) leftovers.push(e.name); } };
    walk(root);
    assert.deepEqual(leftovers, []);
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("sites migrated to atomicWriteDurable no longer hand-roll a rename publish", () => {
  for (const rel of ["storage/snapshot_store.js", "storage/overlay_store.js", "view/authority.js"]) {
    const text = readFileSync(join(SRC_ROOT, rel), "utf8");
    assert.ok(text.includes("atomicWriteDurable("), `${rel} must publish through atomicWriteDurable`);
    assert.ok(!/renameSync\(/.test(text), `${rel} must not call renameSync directly`);
  }
});

test("concurrent atomicWriteDurable writers to one path leave one intact file and no temp files", async () => {
  const { atomicWriteDurable } = await import(pathToFileURL(join(SRC, "directory_fsync.js")).href);
  const root = mkdtempSync(join(tmpdir(), "spipe-atomic-"));
  try {
    const target = join(root, "a", "b", "out.json");
    const payloads = Array.from({ length: 32 }, (_, i) => `{"writer":${i}}`.padEnd(4096, " "));
    await Promise.all(payloads.map(async (p) => atomicWriteDurable(target, p)));
    assert.ok(payloads.includes(readFileSync(target, "utf8")), "final content is exactly one writer's payload");
    assert.deepEqual(readdirSync(join(root, "a", "b")), ["out.json"]);
  } finally { rmSync(root, { recursive: true, force: true }); }
});
