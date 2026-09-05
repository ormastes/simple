# spipe plugin/MCP surface: e274cd33719 clobbered the modular MCP entrypoint, the plugin descriptor, and the 0.2.0 version bump

**Status:** §1-§4 + §3b RESOLVED 2026-09-05. §5, §6, §7-invariant, §8, §9, §10 OPEN (need an owner).
**Filed:** 2026-09-05 (rewritten same day once git evidence settled the open questions)
**Scope:** `examples/05_stdlib/spipe/`

## Root cause (supersedes the original "version drift" framing)

`e274cd33719 chore: merge all share-history worktree branches into main` (2026-08-30)
is a **single-parent squash**, not a merge. It reverted spipe files to a pre-`b76f7962350`
state. The same clobber is what killed `cli/spipe.js` (a 4-line modular entrypoint replaced
by the old monolith's import header — repaired earlier on 2026-09-05). **Only half was
repaired then**; the MCP half and the plugin descriptor were still clobbered.

Timeline: `185f3303282` modularize CLI+MCP (08-25) -> `b76f7962350` release hardening,
version 0.2.0, +8 release tools, `release_policy_test.js` (08-27) -> `e274cd33719` clobber (08-30).

## §1 RESOLVED — `mcp/server.js` was the stale monolith

At `185f3303282` `mcp/server.js` is **9 lines**, importing `./protocol/router.js` and
`./transport/stdio.js`. `e274` replaced it with the **187-line** monolith that imports
nothing from `mcp/protocol/**` or `mcp/transport/**`, leaving that whole modular tree
dead code. Effect, measured over a real stdio JSON-RPC session:

| | clobbered monolith | restored modular |
|---|---|---|
| `serverInfo.version` | 0.1.0 | 0.2.0 |
| `tools/list` | **6** | **14** |
| release tool family | absent | present (8 tools) |

The entire `spipe_release_*` family — the subject of `b76f7962350` — was unreachable.
**Fixed:** restored the modular entrypoint from `185f3303282`.

## §2 RESOLVED — manifest path base (the original §1 open question)

Answered by git, not by guessing. `b76f7962350`'s `plugin/.codex-plugin/plugin.json` had
`"args": ["../mcp/server.js"]`; `e274` rewrote it to `"mcp/server.js"` **and deleted the
whole `interface` block**. Under plugin root = `plugin/` (parent of `.codex-plugin/`, the
same convention as `tools/claude-plugin/*/.claude-plugin/plugin.json`) both keys then
resolve: `"skills": "./skills/"` -> `plugin/skills/` and `"../mcp/server.js"` ->
`mcp/server.js`. `release_policy_test.js:86` independently pins `descriptor.skills === "./skills/"`.
**Fixed:** restored `plugin.json` from **`0fce018eda3`** (`e274`'s single parent = the true
pre-clobber state). Restoring from `b76f7962350` was wrong and was corrected: `72a466dd6d3`
had since added the scoped-self-review `longDescription` text and a fourth `defaultPrompt`,
which a `b76f` restore silently dropped.

`plugin/manifest.sdn` is a **different file with a different base** and was never wrong:
`scripts/build.shs` resolves `cli/spipe.js`, `mcp/server.js`, `plugin/manifest.sdn` from the
**module root**, so the manifest's unprefixed paths are correct as written.

## §3 RESOLVED — version drift

Not a drift to arbitrate: `b76f7962350` bumped `package.json` **and** `plugin/manifest.sdn`
to 0.2.0, and `e274` reverted both to 0.1.0 while leaving `plugin.json`, `dispatcher.js`
and `mcp/protocol/initialize.js` at 0.2.0. **Single source of truth is `package.json`**
(`release_policy_test.js:33` reads it and compares). Restored to **0.2.0**; all five sites
(`package.json`, `manifest.sdn`, `plugin.json`, `dispatcher.js --version`,
`protocol/initialize.js`) now agree, and `0fce018eda3` independently confirms 0.2.0.

### §3b RESOLVED — `package.json` `files:` lost `src/` and `schema/`

Found only by diffing the whole module against `0fce018eda3` rather than chasing the files
the tests happened to name. `e274` dropped `"src/"` and `"schema/"` from the published
`files:` array. This is causally linked to §1: `mcp/transport/stdio.js:2` imports
`../../src/format/stable.js`, so the modular server needs `src/` at runtime while the
monolith did not — the clobber was internally consistent for the monolith it restored.
Left unrepaired, `npm publish` would have shipped a package whose MCP server cannot start.
**Fixed:** restored both entries.

## §4 RESOLVED — `spipe_release_guide` was 100% dead

`mcp/protocol/tools.js:101` reads `doc/00_llm_process/skill_command/command/release.md`
through `readDoc`, whose allowlist listed five siblings under `doc/00_llm_process/` but
omitted `skill_command/`. The file exists; every call threw
`path is outside the SPipe documentation allowlist`. The CLI's `release-guide` reads the
same file directly and so masked the failure. **Fixed:** added the missing prefix; the tool
now returns 5592 chars. Confirmed **not** clobber damage: `0fce018eda3`'s `tools.js` omits
`skill_command/` from the allowlist too, so this tool had never worked.

## §5 OPEN — legacy fixtures still pin the pre-`b76f` surface

`test/fixture/legacy_cli.json` (`"0.1.0\n"`), `test/fixture/legacy_mcp.json`
(`serverInfo` 0.1.0 + a 6-entry `toolSchemas` deepEqual) and
`test/integration/legacy_workflows_test.js:29-30` were **not** updated by `b76f7962350`,
so `legacy_compat_test` and `legacy_workflows_test` have been red since 08-27,
independently of the clobber for the CLI half. **State this plainly: the MCP half of
`legacy_compat_test` (serverInfo 0.1.0, a 6-entry `toolSchemas` deepEqual) matched the
clobbered monolith exactly, so the §1 restore is what turns that half red.** The fixture is
stale rather than right — it encodes the reverted surface — but the transition is caused by
this work and is not a pre-existing red. Regenerating a *compat baseline* can mask real regressions, so this was **not**
done — an owner should confirm the baseline is meant to track the current surface and
regenerate, or say why 0.1.0/6 tools must be frozen.

## §6 OPEN — `fine-tune-ready` gates unconditionally on app-handoff evidence

`src/cli/fine_tune_status.js:455-466`: the last four checks
(`license_constraints_reviewed`, `safety_eval_complete`, `deployment_evidence_ready`,
`app_handoff_doc_ready`) never consult the attempt's `app_or_server_target`, so an attempt
that targets no app can never be ready. `scripts/build.shs`'s `ready_check.sdn` fixture
(no `app:` section) asserts a PASS and therefore fails. Either the gate should be
conditional on an app/server target, or the fixture needs app evidence. **Not decided here.**

This was invisible until now because `build.shs` aborted long before reaching it — see §7.

## §7 PARTIALLY FIXED — `scripts/build.shs` was dead at line 49

`git -C ../.. ls-files --stage examples/spipe | grep -q '^100'` under `set -eu`: both the
path (`examples/spipe`; the module moved to `examples/05_stdlib/spipe`) and the hop count
(`../..` now resolves to `examples/`, not the repo root) are stale, so `npm run build`
exited 1 with **no output at all** and nothing after line 49 had run since the move. This
is the same stale-`examples/spipe` class as the dangling `.spipe/*` mount symlinks.
**Fixed:** resolve the repo root with `git rev-parse --show-toplevel` and use the real path.
**Fixed:** added the two missing `registry_ready` fixture steps (`fine-tune-record-app` plus
an existing handoff doc) that `fine-tune-ready` requires — verified empirically.
**Host-detection preserved:** the old `git -C ../.. rev-parse` was not just a path, it also
gated the block off in a standalone Spipe clone. The replacement keeps that semantic with
`[ "$repo_root/examples/05_stdlib/spipe" = "$ROOT_DIR" ]` rather than merely testing that
some git repo exists.

**Kept, NOT removed (an earlier pass in this session removed it; that was reverted):** the
`diff -qr <module> <.spipe/spipe>` identity assertion, restored with corrected paths. Filing
an owner decision is the brief; making it unilaterally is not. It is the assertion
`build.shs` now stops at, because the two trees have genuinely diverged — `.spipe/spipe` is
the compatibility submodule pinned at `c2a50b9` and lacks
`release.md`/`software-release.md`/`sync.md` from `b76f7962350`, while
`check-spipe-submodule-gitlinks.shs` (the authoritative gate) treats the two as separate and
passes. **Owner decision needed:** is the module still required to be byte-identical to the
compatibility submodule, or is that invariant obsolete and to be deleted?

`build.shs` therefore still exits 1, now at the `diff -qr` above; §6's `ready_check` is the
next failure behind it.

## §8 OPEN (pre-existing, not spipe-caused) — "GitHub forbids a PR author" content gap

`release_policy_test.js:196` requires that string in
`examples/05_stdlib/spipe/doc/00_llm_process/skill_command/command/release.md`; it is
absent there at HEAD **and** at `b76f7962350`, and lives only in the host repo's
*software-release* skills (`.claude/skills/software-release.md`, `.codex/`, `.agents/`).
That doc is generated (`<!-- llm-process-gen: managed source=claude_release_command -->`),
so this is a generation-sync gap, possibly an assertion pointed at the wrong file.
The repo guard `scripts/check/check-self-review-guidance.shs` fails on the same string in
the untouched `doc/07_guide/infra/self_review_policy_db.md`, confirming it is a pre-existing
repo-wide gap unrelated to this work.

## §9 Note — `.mcp.json` advertises a `spipe` tool that does not exist

`.mcp.json`'s `_info` for the spipe server lists "spipe_info, spipe_experts, spipe_read_doc,
spipe_fine_tune_*, **spipe**". There is no tool named `spipe` in the 14 advertised. Cosmetic,
but it misleads callers. Both registrations (`.mcp.json` and `~/.codex/config.toml`) point at
`examples/05_stdlib/spipe/mcp/server.js` and remain correct — the restore changed that file's
contents, not its path.

## Retained from the original record

`check-mcp-wrapper-contract.shs` passes, but its fixtures hardcode the triple
`x86_64-unknown-linux-gnu` (script lines ~95-204), so on this aarch64 host its green verdict
says nothing about the real `bin/simple_mcp_server` wrapper or the real
`bin/release/aarch64-unknown-linux-gnu/` layout. Not a false PASS — it is a self-test and
passes as one — but do not read it as coverage of the host wiring.


## §10 OPEN (pre-existing, outside the plugin/CLI/MCP surface) — 19 unit failures in `src/**`

Recorded so the next session does not rediscover them. `node --test test/unit/*.js`:
**before this work 171 tests / 150 pass / 21 fail; after, 171 / 152 / 19** — the two
recovered are exactly `plugin release schemas and identities stay at 0.2.0` (§3) and
`CLI, MCP, manifest, and plugin descriptor expose the same release policy` (§2). No test
regressed.

The remaining 19 are a separate defect class, not the plugin surface: module-level
`SyntaxError`s from **duplicated declarations**, e.g.
`src/workspace/registry.js` carries `export function isWorkspaceRegistryV1` **three times**
(`0fce018eda3` has it once), which is a concatenation-style clobber rather than a revert.
Affected suites: `authorization_cursor_receipt`, `knowledge_compiler_commit_publisher`,
`search_lexical_source`, `search_rerank_evidence`, `search_reranker_pair_evidence`,
`search_reranker`, `snapshot_authority_projection_port`, `snapshot_authority`,
`target_inventory_store`, `unicode_17_tables`, `view_uri`, `wave5_read_authority`,
`wave5_snapshot_authority`, `workspace_storage`, plus §8's `canonical release guidance`.

Deliberately not repaired here: it is outside the plugin/CLI/MCP/host-mount scope this
session was given, and the whole-module diff against `0fce018eda3` shows HEAD is **ahead**
of that parent by 99 files / +5719 lines (the squash also landed the wave4/wave5 work), so
these files cannot be restored wholesale from the parent — each needs a per-file de-dup
against its pre-squash content.
