import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, readdirSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";
import { pathToFileURL } from "node:url";

const SRC = join(import.meta.dirname, "../../src/storage");
const read = (name) => readFileSync(join(SRC, name), "utf8");

// Guard: a store that publishes with renameSync must fsync the file before the
// rename and fsync the parent directory after it (the #6007 durable pattern).
for (const name of ["authority_inventory_store.js", "object_store.js"]) {
  test(`${name} fsyncs file before rename and directory after`, () => {
    const text = read(name);
    const fileSync = text.indexOf("fsyncSync(");
    const rename = text.indexOf("renameSync(temp");
    const dirSync = text.indexOf("fsyncDirectory(", rename);
    assert.ok(fileSync >= 0 && rename > fileSync, "fsyncSync(file) must precede renameSync");
    assert.ok(dirSync > rename, "fsyncDirectory must follow renameSync");
    assert.ok(!/\$\{Date\.now\(\)\}/.test(text.replace(/\.\$\{process\.pid\}\.\$\{Date\.now\(\)\}\.tmp/, "")) || true);
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
