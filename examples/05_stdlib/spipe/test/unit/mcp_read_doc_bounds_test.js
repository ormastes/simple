import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";

import { callTool } from "../../mcp/protocol/tools.js";

function makeModuleRoot() {
  const root = mkdtempSync(join(tmpdir(), "spipe-mcp-doc-bounds-"));
  mkdirSync(join(root, "doc/00_llm_process/spipe"), { recursive: true });
  mkdirSync(join(root, "doc/00_llm_process/project_expert"), { recursive: true });
  return root;
}

test("readDoc refuses documents over the 256 KiB token-reduction cap", () => {
  const root = makeModuleRoot();
  try {
    const atCap = "# ok\n" + "y".repeat(256 * 1024 - 6);
    writeFileSync(join(root, "doc/00_llm_process/spipe/at-cap.md"), atCap);
    assert.equal(callTool(root, "spipe_read_doc", { path: "doc/00_llm_process/spipe/at-cap.md" }).content[0].text, atCap);

    writeFileSync(join(root, "doc/00_llm_process/spipe/over.md"), "# big\n" + "x".repeat(256 * 1024));
    assert.throws(
      () => callTool(root, "spipe_read_doc", { path: "doc/00_llm_process/spipe/over.md" }),
      /byte SPipe documentation cap/
    );
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("readDoc pins reads to the real module root (symlink escape refused, in-tree symlink ok)", () => {
  const root = makeModuleRoot();
  const outside = mkdtempSync(join(tmpdir(), "spipe-mcp-doc-outside-"));
  try {
    writeFileSync(join(root, "doc/00_llm_process/spipe/inside.md"), "in-tree\n");
    writeFileSync(join(outside, "secret.md"), "escaped\n");
    symlinkSync(join(outside, "secret.md"), join(root, "doc/00_llm_process/spipe/escape.md"));
    symlinkSync(join(root, "doc/00_llm_process/spipe/inside.md"), join(root, "doc/00_llm_process/spipe/link.md"));

    assert.throws(
      () => callTool(root, "spipe_read_doc", { path: "doc/00_llm_process/spipe/escape.md" }),
      /resolves outside the SPipe module/
    );
    assert.equal(
      callTool(root, "spipe_read_doc", { path: "doc/00_llm_process/spipe/link.md" }).content[0].text,
      "in-tree\n"
    );
  } finally {
    rmSync(root, { recursive: true, force: true });
    rmSync(outside, { recursive: true, force: true });
  }
});

test("readDoc rejects non-regular files and non-string paths", () => {
  const root = makeModuleRoot();
  try {
    assert.throws(
      () => callTool(root, "spipe_read_doc", { path: "doc/00_llm_process/spipe/" }),
      /not a regular file/
    );
    assert.throws(
      () => callTool(root, "spipe_read_doc", { path: 42 }),
      /relative path inside the SPipe module/
    );
    assert.throws(
      () => callTool(root, "spipe_read_doc", { path: "doc/00_llm_process/spipe/../spipe" }),
      /relative path inside the SPipe module/
    );
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("spipe_experts truncates oversized expert directories with an explicit remainder marker", () => {
  const root = makeModuleRoot();
  try {
    for (let i = 0; i < 70; i++) mkdirSync(join(root, `doc/00_llm_process/project_expert/expert_${String(i).padStart(3, "0")}`));
    const text = callTool(root, "spipe_experts", {}).content[0].text;
    const line = text.split("\n").find((entry) => entry.startsWith("project_expert="));
    const listed = line.slice("project_expert=".length).split(",");
    assert.equal(listed.length, 65);
    assert.equal(listed[64], "…(+6 more)");
    assert.match(text, /domain_expert=\ntool_expert=/);
  } finally { rmSync(root, { recursive: true, force: true }); }
});
