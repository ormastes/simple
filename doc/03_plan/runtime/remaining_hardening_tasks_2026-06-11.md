# Remaining Hardening Tasks — Small-Task Replan (2026-06-11)

Everything left open after the E1–E7 escalations and the follow-up wave
(`escalation_fixes_2026-06-11.md` FINAL STATUS), broken into small,
independently verifiable tasks. Execution: parallel Sonnet agents, disjoint
scopes, Fable verifies + commits per batch with pull-rebase-push.

## Wave 1 (parallel, disjoint scopes)

### S1 — std.shell exist-after-create returns false  [pure Simple]
Bug doc: `std_shell_file_dir_ops_false_2026-06-11.md`. 4 of 9 tests red in
`test/01_unit/lib/std/shell/file_system_spec.spl` (file.exist after create,
dir create/remove, recursive mkdir, dir listing) while write/read/copy/rename
pass. Root-cause the std.shell wrappers vs the io_runtime primitives the
passing tests use (suspect path-normalisation or wrapper dispatch). Fix at
root cause; spec must go 9/9 honestly. Scope: src/lib std.shell wrapper
modules + that spec + bug doc.

### S2 — FAT32 wave-4c: wire read() through read_cluster_chain  [pure Simple]
Bug doc `fat32_no_cycle_guard_chain_walk_2026-06-11.md` open item FINDING-T1.
Thread `dev` through `read()`'s signature in src/os/kernel/fs/fat32.spl so
file reads walk the guarded chain instead of serving only the cached
root_dir_data. Update all read() callers. Keep mount-time fast path if cheap.
Extend fat32_chain_walk_spec or add fat32_read_spec: multi-cluster file read
assembles correct bytes; corrupt chain surfaces Err (no hang). Scope:
fat32.spl + its callers + spec + bug doc.

### S3 — Lean FINDING-U2: recursive stacking-tree proof  [Lean only]
src/verification/ui_compositor: model currently flattens ONE stacking level.
Add the recursive tree model (StackingCtx children) and prove
flattenPaintOrder over the recursive tree is a permutation of all surfaces
(extends T6). Zero sorry, lake build green. Scope: ui_compositor project only
— do NOT touch stacking.spl.

### S4 — worker.spl gc_boundary tier-import errors  [pure Simple]
3 pre-existing errors at src/lib/nogc_async_mut/http_server/worker.spl lines
~36/78/84: nogc_async_mut importing std.nogc_sync_mut.io.{tcp,file_ops,
time_ops} directly. Fix per tier rules: add/use nogc_async_mut io wrapper
modules (export-use pattern; nogc_async_mut is the default tier and already
has an io hub — check src/lib/nogc_async_mut/io/). worker.spl must lint with
0 gc_boundary errors; http_server specs (phase_result_headers 16/16, csrf
24/24) stay green. Scope: nogc_async_mut io wrappers + worker.spl imports.

### S5 — Seed small batch: B6 await type + SPIPE006 message  [Rust seed]
(a) B6: compiler/src/hir/lower/expr (~lines 193–200) hardcodes TypeId::I64
for await; infer from the operand type instead (identity under eager async).
Rust test pinning a non-i64 await type. (b) SPIPE006 duplicate message in
driver/src/cli/code_quality.rs:224 — recommend assert_true(condition), align
with the .spl lint fix (27c44e3780). cargo test scoped; cargo build --release;
verify fresh binary on an await-non-i64 repro; NO deploy (orchestrator
deploys). Scope: those two Rust files + tests + bug doc updates.

## Wave 2 (after wave 1 — dependencies/conflicts)

### S6 — Seed B3/B3b: generator/actor desugar class not in HIR scope
Triaged root cause (bug doc async_await_interpreter_crashes_2026-06-11.md):
HIR lowering runs before desugar-injected classes are in scope. Fix the
ordering or symbol registration in src/compiler_rust/compiler/src/hir/lower/.
STOP-and-document if it requires re-architecting lowering. Unlocks S7.
(Same dir as S5's B6 edit — serialized to wave 2.)

### S7 — Fill async_integration_spec honestly (C2)
21 vacuous expect(1).to_equal(1) tests. Blocked on S6; once generators/actors
lower, replace each vacuous body with a real assertion per its description.

### S8 — Seed B5: Promise vs FutureValue reconcile
value_async.rs + async_gen.rs dual representation; masked by eager-async
identity. Unify or document the canonical type; Rust tests for cross-path
await. Independent of S6 but same crate — wave 2 to avoid cargo lock contention.

### S9 — FAT32 wave-4d: allocator + crossLinkFree wiring
Implement cluster allocation (write path), wire to the Lean crossLinkFree
invariant (new theorem). Same file as S2 — must follow it.

### S10 — Stage4 broader spec validation (bootstrap deploy gate)
Run the broader spec set under the stage4 self-hosted chain (memory:
project_bootstrap_deploy_pending) and report deltas vs the Rust seed —
the remaining gate before self-hosted deploy. Heavy; run solo.

## Out of scope (blocked)
- selfhosted_mcp_binary_segfault — unblocks only after S10 + deploy.
