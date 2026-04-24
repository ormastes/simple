# native-mcp-build-bootstrap -- Completion Report

**Date:** 2026-04-24
**Pipeline:** SStack 8-phase

## Summary

Added native compilation targets for MCP servers (`simple_mcp_server`, `simple_lsp_mcp_server`) to the bootstrap pipeline. `bootstrap-from-scratch.sh --deploy` now produces platform-native MCP server binaries alongside the main CLI binary, solving the Linux/Windows gap where only pre-built macOS aarch64 binaries previously existed.

## Architecture

- **Stage 5 after Stage 4**: MCP builds run sequentially after full CLI build, using the same `stage_for_build` compiler and `stage4_backend`.
- **Non-blocking failure**: MCP build failure does not block CLI deploy — `set +e`/`set -e` wraps each MCP build; warning is printed, CLI is always deployed.
- **`--no-mcp` flag**: Skips Stage 5 entirely; useful for CI jobs that only need the CLI binary.
- **DRY loop**: Both Stage 5a/5b are implemented as a `for` loop over `name:entry` pairs, not copy-paste blocks.
- **Zero-byte guard**: Both scripts check `[ -s ... ]` (non-empty) after successful exit code to catch empty-file edge case.
- **setup.sh three-step detection**: Native binary detection checks `(a)` target is a real binary → keep it; `(b)` `build/native/` source → copy; `(c)` generate shell wrapper fallback. Prevents overwriting bootstrap-deployed native binaries.
- **`build mcp` CLI subcommand**: Deferred per architecture decision — bootstrap scripts provide equivalent functionality.

## Files

- **Specs:** `test/system/bootstrap_mcp_spec.spl` (13 SSpec tests, 4 groups)
- **Implementation:**
  - `scripts/bootstrap/bootstrap-from-scratch.sh` — Stage 5, deploy extension, `--no-mcp` flag
  - `scripts/bootstrap/bootstrap-windows.sh` — Stage 5 with `.exe` suffix and `--clean`, `--no-mcp` flag
  - `scripts/setup.sh` — Three-step native binary detection in MCP launcher generation
- **State:** `.sstack/native-mcp-build-bootstrap/state.md`

## Verification

- Tests: 13 SSpec tests (4 groups) covering AC-1, AC-3, AC-5, AC-7; 17 shell integration tests covering AC-1 through AC-7
- Lint: `bash -n` syntax check PASS on all three scripts
- Build check: `bin/simple build check` exit 0
- AC-2 (`build mcp` CLI subcommand): explicitly deferred per architecture decision with documented rationale

## Acceptance Criteria

| AC | Status | Notes |
|----|--------|-------|
| AC-1 | PASS | Stage 5 produces `bin/release/<triple>/simple_mcp_server` and `simple_lsp_mcp_server` |
| AC-2 | DEFERRED | `build mcp` CLI subcommand deferred; bootstrap scripts provide equivalent functionality |
| AC-3 | PASS | setup.sh preserves bootstrap-deployed native binaries; existing symlink loop unchanged |
| AC-4 | PASS | `.mcp.json` uses `bin/simple_mcp_server` symlinks; no hardcoded platform paths |
| AC-5 | PASS | JSON-RPC initialize tested in SSpec Group 3 and shell T4 tests |
| AC-6 | PASS | `bootstrap-windows.sh` Stage 5 builds `.exe` MCP binaries |
| AC-7 | PASS | Stage 5 is additive; Stage 4 unchanged; MCP failure non-blocking |

## Timeline

| Phase | Status | Date |
|-------|--------|------|
| 1. Intake | done | 2026-04-13 |
| 2. Research | done | 2026-04-13 |
| 3. Architecture | done | 2026-04-13 |
| 4. Spec | done | 2026-04-13 |
| 5. Implement | done | 2026-04-13 |
| 6. Refactor | done | 2026-04-13 |
| 7. Verify | done | 2026-04-13 |
| 8. Ship | done | 2026-04-24 |

## Commits

- `ba07eb674a` — feat(bootstrap): add native MCP server compilation to bootstrap pipeline
- `107f4b9976` — chore: update MCP/T32 symlinks after bootstrap deploy
