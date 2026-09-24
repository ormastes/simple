#!/usr/bin/env node
import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { readDoc } from "../../mcp/protocol/tools.js";

const root = mkdtempSync(join(tmpdir(), "spipe-mcp-security-"));
const outside = mkdtempSync(join(tmpdir(), "spipe-mcp-outside-"));

try {
  mkdirSync(join(root, "doc/00_llm_process/spipe"), { recursive: true });
  writeFileSync(join(root, "README.md"), "# allowed\n");
  writeFileSync(join(outside, "secret.md"), "legacy-symlink-target\n");
  writeFileSync(join(root, "doc/00_llm_process/spipe/inside.md"), "in-tree-target\n");
  writeFileSync(join(root, "doc/00_llm_process/spipe/big.md"), "# big\n" + "x".repeat(256 * 1024 + 1));
  symlinkSync(outside, join(root, "doc/00_llm_process/spipe/external"));
  symlinkSync(join(root, "doc/00_llm_process/spipe/inside.md"), join(root, "doc/00_llm_process/spipe/internal-link.md"));

  assert.equal(readDoc(root, "README.md"), "# allowed\n");
  assert.throws(() => readDoc(root, "../README.md"), /relative path inside/);
  assert.throws(() => readDoc(root, "/etc/passwd"), /relative path inside/);
  assert.throws(() => readDoc(root, "\\server\\share"), /relative path inside/);
  assert.throws(() => readDoc(root, "package.json"), /outside the SPipe documentation allowlist/);
  assert.throws(() => readDoc(root, "doc/00_llm_process/spipe/missing.md"), /document not found/);

  // Hardened contract (deliberate fixture update): lexical allowlisting is
  // backed by realpath containment, so a whitelisted directory can no longer
  // symlink outside the module and leak arbitrary files.
  assert.throws(() => readDoc(root, "doc/00_llm_process/spipe/external/secret.md"), /resolves outside the SPipe module/);
  // In-tree symlinks still resolve and read normally.
  assert.equal(readDoc(root, "doc/00_llm_process/spipe/internal-link.md"), "in-tree-target\n");
  // Token-reduction caps: oversized documents and directories are refused.
  assert.throws(() => readDoc(root, "doc/00_llm_process/spipe/big.md"), /256 KiB|byte SPipe documentation cap/);
  assert.throws(() => readDoc(root, "doc/00_llm_process/spipe/"), /not a regular file/);
  console.log("STATUS: PASS spipe-legacy-mcp-read-security-contract");
} finally {
  rmSync(root, { recursive: true, force: true });
  rmSync(outside, { recursive: true, force: true });
}
