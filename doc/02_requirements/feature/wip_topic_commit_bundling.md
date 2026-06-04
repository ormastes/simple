# WIP Topic-Aware Commit Bundling Helper

**Type:** Feature
**Category:** DX / VCS / Tooling
**Priority:** Medium
**Proposed:** 2026-04-16
**Status:** Proposed

## Problem

When the working copy contains uncommitted changes spanning **multiple unrelated topics**, the user must manually decide which files belong together. Today this requires:

1. `jj diff --stat` to list modified files
2. Mental model of which files relate to which feature/fix
3. `jj split` or staged `jj commit` flows to break things apart
4. Hand-crafted commit messages

Concrete incident (2026-04-16, this session): pre-`/sync`, the working copy contained:
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`  (RSA-PSS verify)
- `src/compiler_rust/compiler/src/interpreter_extern/signatures.rs`  (RSA-PSS verify)
- `src/compiler_rust/runtime/src/value/ffi/signature.rs`  (RSA-PSS verify)
- `src/os/tls13/cert_verify.spl`  (RSA-PSS callsite)
- `config/mcp/mcp_startup_lib.sh`  (MCP wrapper hardening)
- `src/app/mcp/main.spl`, `src/app/mcp/main_lazy_*.spl` (×5)  (MCP source fixes)
- `src/app/simple_lsp_mcp/json_helpers.spl`  (LSP MCP source fix)
- `build/native/*_native.broken.20260416` (×2)  (native binary quarantine)
- `build/native/README`  (broken-binary doc)

The agent had to ask the user "bundle as one commit or two?" because there was no automatic way to detect that the first 4 files form an `tls13/rsa-pss` topic and the last 8 form an `mcp` topic.

## Proposed Solution

A new subcommand `simple commit --auto-bundle` (and matching MCP tool `simple_commit_bundle`) that:

### 1. Topic detection

Group modified files by:
- **Path prefix clustering** (e.g., `src/app/mcp/*` and `config/mcp/*` → topic `mcp`; `src/compiler_rust/*/signature.rs` and `src/os/tls13/*` → topic `tls13/crypto`)
- **Symbol-graph proximity** (functions/extern fns mentioned in modified hunks; if the modified region of `cert_verify.spl` references `rt_rsa_pss_*` newly added in `signatures.rs`, the two are co-topic)
- **Commit-message prior** (recent commits' file sets and their `feat(scope):`/`fix(scope):` scopes serve as cluster centroids)

Output (default = dry-run):
```
$ simple commit --auto-bundle --dry-run
Detected 2 topics in 12 modified files:

[1/2] tls13/rsa-pss (4 files)
  M src/compiler_rust/compiler/src/interpreter_extern/mod.rs
  M src/compiler_rust/compiler/src/interpreter_extern/signatures.rs
  M src/compiler_rust/runtime/src/value/ffi/signature.rs
  M src/os/tls13/cert_verify.spl
  → suggested: feat(tls13/rsa-pss): RSA-PSS SHA{256,384,512} verify wired into TLS 1.3 cert path
  → confidence: 0.92  (3-of-3 RSA-PSS extern fns introduced together; cert_verify is sole consumer)

[2/2] mcp (8 files)
  M config/mcp/mcp_startup_lib.sh
  M src/app/mcp/main.spl
  M src/app/mcp/main_lazy_protocol.spl
  M src/app/mcp/main_lazy_vcs_tools.spl
  M src/app/mcp/main_lazy_dialog_tools.spl
  M src/app/mcp/main_lazy_diag_tools.spl
  M src/app/mcp/main_lazy_debug_tools.spl
  M src/app/simple_lsp_mcp/json_helpers.spl
  R build/native/simple_mcp_native → simple_mcp_native.broken.20260416
  R build/native/simple_lsp_mcp_native → simple_lsp_mcp_native.broken.20260416
  A build/native/README
  → suggested: fix(mcp): wrapper sentinel cache + extern fn declarations + native binaries quarantined
  → confidence: 0.81  (mcp/ + simple_lsp_mcp/ + build/native/ co-modified; native rename references in README)

Apply? [y/N/edit]
```

### 2. Interactive refinement

- `[edit]` opens an `$EDITOR` session listing topics; user can re-assign files between topics or split a topic further.
- `--accept-all` skips confirmation (for scripted sync flows).
- `--single` forces all files into one commit (escape hatch).

### 3. Commit-message draft synthesis

For each topic:
- Look at the **diff hunks** (added/removed identifiers, new extern declarations, new test files).
- Apply the existing "Commit Types" rule (`feat`, `fix`, `refactor`, …) by detecting:
  - New `fn`/`extern fn` declarations → `feat`
  - `error|fix|crash|undefined|null` keywords in hunks → `fix`
  - Pure rename/move without behavior change → `refactor`
- Match the project's commit-style: short scope, imperative subject, ≤72 chars.

### 4. MCP tool surface

```
simple_commit_bundle      # detect + propose (read-only)
simple_commit_bundle --apply  # actually commit each topic in order
```

Returns structured JSON per topic so an agent can present each commit for individual approval.

## Integration with `/sync`

Update `.claude/skills/sync/SKILL.md` to call `simple commit --auto-bundle --dry-run` as step 1 instead of "commit local changes (if any)". The agent can then ask the user once per topic instead of once per ambiguity.

## Implementation Notes

- **Topic graph data structure:** a UnionFind over modified files, with edges weighted by:
  - Path prefix share (Jaccard on path components)
  - Symbol co-mention count (extracted via `simple ast-query`)
  - Same-line neighborhood in `git log -p` of recent commits
- **Caching:** topic detection should run in <500 ms for ≤50 modified files; cache the symbol index in `.simple/cache/topic_index/`.
- **No false-merge:** when confidence < 0.6, prefer to leave files in a separate "uncategorized" topic and prompt the user, rather than over-bundle.

## Acceptance Criteria

- [ ] `simple commit --auto-bundle --dry-run` on the 12-file scenario above produces exactly the 2 topics shown.
- [ ] Confidence scores are reproducible (same input → same output).
- [ ] `--accept-all` produces 2 separate commits in the right order (no orphan; rebase-friendly).
- [ ] Edge case: 1 file modified → 1 topic, no prompt.
- [ ] Edge case: 50 files in 1 directory → 1 topic if symbols are tightly coupled, multiple otherwise.

## Why Not Just `jj split`?

- `jj split` requires the user to already know the partition; the helper *discovers* it.
- `jj split` doesn't draft messages.
- `jj split` is interactive in the TUI; not friendly to MCP/agent automation.

## Related

- `simple_cli_mcp_completeness.md` — broader CLI/MCP parity push.
- `simple_lsp_visibility_support.md` — symbol-graph infrastructure overlap.
- `repo_and_pull_req` skill — the `/sync` workflow this would integrate with.

## Out of Scope

- Cross-repo/submodule bundling.
- Authoring full body paragraphs for commit messages — only subject + bullet list.
