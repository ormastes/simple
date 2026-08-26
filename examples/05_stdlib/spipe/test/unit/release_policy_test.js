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
  assert.match(manifest, /immutable_release_candidates: true/);
  assert.match(manifest, /promote_without_rebuild: true/);
});

test("MCP exposes read-only release policy surfaces", () => {
  assert.ok(tools.some((tool) => tool.name === "spipe_release_guide"));
  assert.ok(tools.some((tool) => tool.name === "spipe_release_capabilities"));
  const capabilities = callTool(root, "spipe_release_capabilities").content[0].text;
  assert.match(capabilities, /immutable_release_candidates=true/);
  assert.match(capabilities, /promote_without_rebuild=true/);
});

test("CLI, MCP, manifest, and plugin descriptor expose the same release policy", () => {
  const manifest = readFileSync(join(root, "plugin/manifest.sdn"), "utf8");
  const descriptor = JSON.parse(readFileSync(join(root, "plugin/.codex-plugin/plugin.json"), "utf8"));
  const dispatcher = readFileSync(join(root, "src/cli/dispatcher.js"), "utf8");
  const mcpCapabilities = callTool(root, "spipe_release_capabilities").content[0].text;
  for (const capability of [
    "isolated_sessions",
    "reviewed_beta_backports",
    "immutable_release_candidates",
    "promote_without_rebuild"
  ]) {
    assert.match(manifest, new RegExp(`${capability}: true`));
    assert.match(dispatcher, new RegExp(`capability\\.${capability}=true`));
    assert.match(mcpCapabilities, new RegExp(`${capability}=true`));
  }
  for (const path of [
    "../.claude/skills/software-release.md",
    "../.claude/skills/release.md",
    "../.claude/skills/sync.md",
    "../.codex/skills/software-release/SKILL.md",
    "../.codex/skills/release/SKILL.md",
    "../.codex/skills/sync/SKILL.md"
  ]) assert.ok(descriptor.skills.includes(path), `missing installed skill: ${path}`);
  for (const path of [
    "../.gemini/commands/release.toml",
    "../.gemini/commands/sync.toml"
  ]) assert.ok(descriptor.commands.includes(path), `missing installed command: ${path}`);
});

test("canonical release guidance rejects legacy unsafe behavior", () => {
  const paths = [
    "doc/00_llm_process/skill_command/command/release.md",
    "doc/00_llm_process/skill_command/skills/codex/release/skill.md",
    "doc/00_llm_process/skill_command/skills/gemini/release/skill.md",
    "doc/00_llm_process/skill_command/skills/pipe/release/skill.md",
    "doc/00_llm_process/skill_command/skills/pipe/release/repo_and_pull_req/skill.md"
  ];
  const guide = readFileSync(join(root, paths[0]), "utf8");
  for (const path of paths) {
    const content = readFileSync(join(root, path), "utf8");
    for (const forbidden of ["git push --tags", "bookmark set main", "gh release delete", "git tag -d", "NO BRANCHES"])
      assert.equal(content.includes(forbidden), false, `${path}: forbidden legacy command: ${forbidden}`);
  }
  assert.match(guide, /reviewed bug-fix commit/);
  assert.match(guide, /Promotion never rebuilds/);
});
