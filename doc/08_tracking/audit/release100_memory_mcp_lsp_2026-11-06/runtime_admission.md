# release/1.0.0 verification admission audit — 2026-11-06

Read-only inspection; no builds, broad tests, merges, or modifications to another lane.

## Deployed runtime

`/Users/ormastes/simple/bin/release/aarch64-apple-darwin/simple` has SHA256 `f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc`, July 25 mtime, and prints `Simple v1.0.0-beta` with exit 0. No adjacent provenance/admission receipts exist. Its strings contain 162 `/rustc/` and 379 `compiler_rust` markers. This is insufficient evidence of an admitted pure-Simple Stage 4 CLI; do not report release gates using it as proven self-hosted evidence.

## Current admitted candidate

Path: `/private/tmp/boot4-out/s2/stage3/aarch64-apple-darwin/stage2-admitted/simple`.
SHA256: `d05b5bcf561e6fee3a9a55af67ec86a57d11fe78a995e9e77dd6b8bb188f892e`.
Receipt: adjacent `admission.env`, schema `simple-bootstrap-stage2-admission-v2`, status `admitted`, identity `d0c1de475f56fde005e6c6c1954c35215c213f0084bda494987b1a24cf30943a`.
Source snapshot: `/private/tmp/boot4-out/s2/stage3/aarch64-apple-darwin/source-inputs-before.txt`, hash `910b8c18a36a1b4274b59d0dfa2d4590a44bcf8a87fdc3efa9fe51d80980b116`.
Source worktree: `/private/tmp/boot4-wt`; recorded HEAD `d3d524f8b4a06a4e5122fdfe881f3b6a86fcefbe`, dirty fingerprint `33ad2bece6de25ff8ed1f84719162e078bb64e32a731d9fcd42ab6ece740a67d`.
Runtime snapshot hash: `a4baee2ee8ad4775697c69740c5f43386666738cb3c11a42285fcb21172e68ec`.
The candidate, source snapshot, runtime snapshot, and sanity receipt hashes were independently checked once and all match the admission receipt. Sanity status is pass, version `simple-bootstrap 1.0.0-rc.1`.

This is a minimal Stage 2 compiler, not Stage 4. It may support isolated native-build compiler probes with recorded stage-scoped evidence. It does not authorize general test/check/SPipe/docgen/release claims. `bootstrap_main.spl` dispatch advertises native-build and compile; no full CLI admission is inferred.

## Live full CLI campaign

PID 25734 remains live under watchdog PID 25700 and outer phase verifier PID 24056. At observation it had run about 39 minutes, consumed approximately 6 GiB RSS and 96% CPU. Command uses the admitted candidate snapshot to native-build `src/app/cli/_CliMain/main_and_help.spl`, LLVM, low-memory, one thread, timeout 3600, in the other lane's isolated caches.

Log: `/private/tmp/boot4-out/s2/stage2-compiler-tests/aarch64-apple-darwin/verification/logs/compiler_cli_build.log`.
Observed tail: HIR 2687/3060 modules, zero failures. This proves live progress, not completion.
Expected CLI: `/private/tmp/boot4-out/s2/stage2-compiler-tests/aarch64-apple-darwin/verification/outputs/compiler-tools/stage2/d05b5bcf561e6fee/f9beeef687527703/simple_cli`.
Summary: `/private/tmp/boot4-out/s2/stage2-compiler-tests/aarch64-apple-darwin/verification/summary.env`; only compiler-version PASS was observed.
No `/private/tmp/boot4-out/s2/stage4` exists. Bounded searches of boot3-out, boot4-out, and build/bootstrap found Stage 2 receipts but no admitted Stage 4 candidate. Absence is scoped to these inspected locations.

Action: coordinate with this campaign owner and consume its actual terminal receipt. Do not duplicate, interrupt, or promote a merely built CLI to Stage 4 admission. If full CLI verification remains unavailable, retain runtime-dependent criteria as blocked while implementing and statically reviewing independent changes.

## Focused verification plan

Use an admitted full runtime with isolated caches/logs. Run each unchanged acceptance gate once.
- Focused changed specs; lint changed SPL; duplicate-check owned directories; SPipe manual and requirement traceability review.
- `<runtime> check src/compiler`, `check src/lib`, `check src/app/mcp`, `check src/app/simple_lsp_mcp`.
- `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`.
- `sh scripts/check/check-core-runtime-smoke.shs <runtime>`.
- `SIMPLE_BINARY=<runtime> MCP_SERVER=<fresh-mcp> LSP_MCP_SERVER=<fresh-lsp> sh scripts/check/check-mcp-native-smoke.shs`.
- Working and staged direct-env-runtime guards; verify no executable specs under doc/06_spec.
- Release-bound whole suite: `bin/simple test test --whole --mode=interpreter`.
- Packaging changes additionally require native MCP/LSP builds and isolated npm package smoke.
- Warm startup, representative request latency, RSS, cache invalidation evidence must match the plan requirements; smoke tests alone are insufficient.

## Landing

`.claude/rules/vcs.md` lines 76–104 and `.spipe/policy/vcs.sdn` allow owner PR-only admin merge on release lines. Push only owned work/* commits, create PR with base release/1.0.0, inspect exact diff and review comments, publish comment review, merge via `gh pr merge <n> --admin --merge`, verify remote merged state, delete topic branch. Never merge genuinely failing changes or unresolved regressions. Tags/publication require separate permission.

Other open release PRs at observation: #7227 observability docs, #7223 UTF8/trace diagnostics, #7220 data-policy. Preserve those lanes.

## Terminal full-CLI child update

A later live-process check found PID 25734 absent (terminal). Its retained log ends with phase 3 FAILED after 4577 sources: `src/app/traceability/query_main.spl:74:5: unresolved name: exit`; one poisoned module, no successful full CLI. This is no longer a verified wait.
The release baseline already imports `std.io_runtime.{exit}` at line 13 and has newer trace-query changes; the campaign source in `/private/tmp/boot4-wt` lacks that import. Do not reapply an already-landed fix or restart the other owner's campaign from stale inputs. A new qualified campaign must consume the repaired source under its owner's immutable-lineage workflow. Full runtime-dependent verification remains blocked; independent source work continues.

The outer verifier subsequently continued with standalone test-runner child PID 35155 (observed live). Only the full-CLI child is terminal; the campaign as a whole was not declared terminal. Standalone runner construction is not full CLI admission.

## Verified no-seed recovery route

The canonical producer's `--validate-parent-only` check succeeded for `/private/tmp/boot4-out/s2/stage2/aarch64-apple-darwin/simple`, with `SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT=/private/tmp`. Freeze the reviewed lane source before a new owned build. Use this actual stage2 parent location, not the copied stage2-admitted location, because parent validation checks the stage layout.

```text
SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT=/private/tmp SIMPLE_BUILD_COMPILER=/private/tmp/boot4-out/s2/stage2/aarch64-apple-darwin/simple sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 --jobs=1 --produce-managed-receipt=release-trust-verification --output=/private/tmp/release100-hardening-bootstrap
```

This refresh preserves the admitted parent's runtime authority and does not request `--full-bootstrap` or the Rust seed. Only after successful fresh admission, resume managed qualification using the emitted `managed-stage4-planner-admission-v2.env` and `--resume-managed-from-admitted=<new-output>`. Verify exact receipt names and identities before execution. A standalone runner cannot authenticate suite evidence without the required CLI/runner owner receipt. The observed old CLI attempt took 2650 seconds and roughly 10 GiB maximum RSS; full cold qualification is an hours-scale prerequisite, not a completed check.
