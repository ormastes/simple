# Target 5/6 completion

Status: OPEN

Owner lane: `codex/target56-isolated`. This TODO carries the unfinished work
from `doc/09_report/compiler/target5_strict_core_hello_2026-09-27.md`,
`doc/09_report/compiler/target6_cold_hir_batch_2026-09-27.md`, and
`doc/08_tracking/bug/target56_isolated_current_source_verification_blockers_2026-09-27.md`.
The isolated changes are groundwork and diagnostics, not production acceptance.

## Target 5 — kernel and extension demand loading

- Produce an ABI-matched current-source pure-Simple Stage4 compiler and runtime
  authority. Resolve the bootstrap failures in the blocker report without
  treating the historical Stage2 binary as release evidence.
- Finish metadata-only optional-provider registration and first-use loading.
  Prove no-import hello maps and initializes zero optional providers, while
  each excluded feature remains usable on first demand.
- Prove exact runtime/link closure for kernel, extensions, aspect packs, and
  native roots. Keep explicit `SIMPLE_LINKER` precedence while qualifying the
  Linux size-mode LLD selection on current source.
- Run the BS7 matched cohorts and Phase 7 one-binary/dynload rows. Require
  Linux stripped hello <=15 KiB **and** <=1.05x same-toolchain C, accepted
  startup/RSS budgets, 30 development or 100 release samples, and empty
  forbidden/optional-provider traces. The historical LLD diagnostic was
  13,944 bytes versus 4,864-byte C hello (2.87x), so the C ratio is open.
- Verify the plain-literal print lowering in a current-source Stage4 hello build:
  confirm the binary no longer retains `rt_string_new_literal`,
  `rt_to_string`, or `rt_literal_intern_table`; then measure paired size,
  startup, and RSS cohorts. The C-entry direct-writer probe is only
  directional evidence (5,152-byte ELF). A same-wrapper, same-root C user
  object probe is 9,168 bytes versus the historical Simple ELF's 13,944;
  it still misses the 1.05x C ceiling by 4,061 bytes and is not completion
  evidence. Review argv and forced runtime roots with exact closure proof.

## Target 6 — persistent compile index

- Build a real cold TLDR/SMF producer from frozen SCV inventory and typed HIR.
  The V2-dependent draft preserved under
  `build/mini_builds/target6_pending_v2/` needs an independently owned,
  committed builder/schema before it can join production source.
- Replace the binding-only empty index with a validated module/package graph,
  variant identity, exact reverse edges, reached SCC schedule, and complete
  action/archive receipts. Route compile, check, bootstrap, native-build,
  MCP/LSP, and daemon requests through one pinned catalog owner; remove warm
  closure scans.
- Qualify the new atomic inventory/cursor `CURRENT` record on a current-source
  runtime. The isolated source now validates filesystem events before publish
  and writes the inventory digest plus Git/filesystem cursor in one pointer
  rename, with a bare-digest legacy reader. The historical Stage2 diagnostic
  native build timed out before an executable was produced. Prove failed
  rename, overflow, event loss, cross-process concurrent writers, cold rebuild, legacy
  migration, and replay recovery without Git or source mutation.
- Run current-source SPipe and native performance cohorts for cold, warm,
  private edit, public edit, SCC, and variant cases. Require exact outputs,
  p95 time and max RSS hard budgets, plus the normalized time/RSS sum rule in
  the optimize skill and guide. The historical cold-HIR batch result
  (normalized sum 0.181595) is diagnostic only.
- The historical Stage2 native scheduler probe panicked with
  `direct-edge-missing:module.000:module.001` on a 64-module chain. Three
  fixture/check cycles produced the same result. The temporary fixture was
  removed and the production scheduler was left unchanged; diagnose this
  under an ABI-matched current-source authority before optimizing scheduling.

Completion requires a `STATUS: PASS` verify report. Stop after three
verify/fix cycles per feature and retain failing logs under `build/mini_builds/`.
