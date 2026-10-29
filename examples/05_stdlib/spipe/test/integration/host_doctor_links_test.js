#!/usr/bin/env node
import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const testRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const moduleRoot = resolve(testRoot, "..");
const cliPath = join(moduleRoot, "cli/spipe.js");
const host = mkdtempSync(join(tmpdir(), "spipe-host-doctor-links-"));
const linkType = process.platform === "win32" ? "junction" : "dir";

function ensureDir(path) {
  mkdirSync(path, { recursive: true });
}

function addDirectoryLink(target, link) {
  ensureDir(dirname(link));
  symlinkSync(target, link, linkType);
}

function replaceDirectoryLink(target, link) {
  rmSync(link, { recursive: true, force: true });
  addDirectoryLink(target, link);
}

function doctor() {
  const result = spawnSync(process.execPath, [cliPath, "doctor", host], {
    cwd: host,
    encoding: "utf8",
    timeout: 10_000
  });
  assert.ifError(result.error);
  return result;
}

try {
  const spipe = join(host, ".spipe");
  const example = join(host, "examples/05_stdlib/spipe");
  const docs = join(host, "doc/llm_process");
  const expertDocs = join(example, "doc/00_llm_process");
  ensureDir(spipe);
  writeFileSync(join(spipe, "config.sdn"),
    "host_process_doc: doc/llm_process\nexample_project_submodule: examples/05_stdlib/spipe\n");

  for (const path of [
    join(spipe, "spipe"),
    example,
    docs,
    join(expertDocs, "domain_expert"),
    join(expertDocs, "template"),
    join(expertDocs, "spipe"),
    join(expertDocs, "project_expert/simple"),
    join(expertDocs, "tool_expert/spipe_submodule")
  ]) ensureDir(path);

  addDirectoryLink(example, join(spipe, "spipe_project"));
  addDirectoryLink(docs, join(spipe, "doc"));
  addDirectoryLink(join(expertDocs, "domain_expert"), join(spipe, "domain_expert"));
  addDirectoryLink(join(expertDocs, "template"), join(spipe, "template"));
  addDirectoryLink(join(expertDocs, "spipe"), join(spipe, "spipe_docs"));
  addDirectoryLink(join(expertDocs, "project_expert/simple"), join(spipe, "project_expert/spipe"));
  addDirectoryLink(join(expertDocs, "tool_expert/spipe_submodule"), join(spipe, "tool_expert/spipe_submodule"));

  const good = doctor();
  assert.equal(good.status, 0, `valid absolute links were rejected:\n${good.stdout}\n${good.stderr}`);
  assert.ok(good.stdout.includes("host_ok doc_link"));
  assert.ok(good.stdout.includes("spipe_doctor=pass"));

  const docLink = join(spipe, "doc");
  const wrongTarget = join(spipe, "wrong_target");
  ensureDir(wrongTarget);
  replaceDirectoryLink(wrongTarget, docLink);
  const wrong = doctor();
  assert.equal(wrong.status, 1);
  assert.ok(wrong.stdout.includes("host_bad_link doc_link"), wrong.stdout);

  replaceDirectoryLink(docs, docLink);
  rmSync(docs, { recursive: true });
  const dangling = doctor();
  assert.equal(dangling.status, 1);
  assert.ok(dangling.stdout.includes("host_bad_link doc_link"), dangling.stdout);
  assert.ok(!dangling.stderr.includes("ENOENT"), dangling.stderr);

  const compatibilityPath = join(spipe, "spipe");
  const compatibilityTarget = join(spipe, "compatibility_target");
  rmSync(compatibilityPath, { recursive: true });
  ensureDir(compatibilityTarget);
  addDirectoryLink(compatibilityTarget, compatibilityPath);
  rmSync(compatibilityTarget, { recursive: true });
  const danglingSubmodule = doctor();
  assert.equal(danglingSubmodule.status, 1);
  assert.ok(danglingSubmodule.stdout.includes("host_missing compatibility_submodule"), danglingSubmodule.stdout);

  console.log("PASS doctor accepts absolute links and reports wrong or dangling targets");
} finally {
  rmSync(host, { recursive: true, force: true });
}
