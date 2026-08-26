import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { initializeResult } from "../../mcp/protocol/initialize.js";
import { tools, callTool } from "../../mcp/protocol/tools.js";

const root = new URL("../../", import.meta.url).pathname;

test("plugin release schemas and identities stay at 0.2.0", () => {
  assert.equal(initializeResult().serverInfo.version, "0.2.0");
  assert.equal(JSON.parse(readFileSync(join(root, "package.json"), "utf8")).version, "0.2.0");
  const manifest = readFileSync(join(root, "plugin/manifest.sdn"), "utf8");
  assert.match(manifest, /version: 0\.2\.0/);
  assert.match(manifest, /reviewed_beta_backports: true/);
});

test("MCP exposes read-only release policy surfaces", () => {
  assert.ok(tools.some((tool) => tool.name === "spipe_release_guide"));
  assert.ok(tools.some((tool) => tool.name === "spipe_release_capabilities"));
  assert.match(callTool(root, "spipe_release_capabilities").content[0].text, /promote_without_rebuild=true/);
});

test("canonical release guidance rejects legacy unsafe behavior", () => {
  const guide = readFileSync(join(root, "doc/00_llm_process/skill_command/command/release.md"), "utf8");
  for (const forbidden of ["git push --tags", "bookmark set main", "gh release delete", "git tag -d"])
    assert.equal(guide.includes(forbidden), false, `forbidden legacy command: ${forbidden}`);
  assert.match(guide, /reviewed bug-fix commit/);
  assert.match(guide, /Promotion never rebuilds/);
});
