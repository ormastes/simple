# W-7 Outer Test Runner Failure Propagation — Done Note

**Status:** NO-OP — already landed before dispatch. Mission spec was stale.
**Date:** 2026-04-26
**Worker:** W-7 (crypto-pure-simple-port wave 3)

## TL;DR

The Phase 2 outer-runner false-green fix the mission asked for is already in
the tree. Commit `f85ca76d8c` ("fix(test-runner): outer runner reports inner
failures correctly") landed on 2026-04-25 22:15Z, **after** the mission spec
was authored ("STILL UNRESOLVED") but **before** W-7 was dispatched. The
in-repo memory note already says **RESOLVED 2026-04-25 (R2-broader Phase 2)**.

I did **not** edit `execution.rs`, `bdd_ffi.rs`, `runner.rs`, `spec.spl`,
`spec/__init__.spl`, or `test_executor_parsing.spl`. Editing them would
risk regressing a working fix for zero gain (CLAUDE.md "NEVER over-engineer").

## What `f85ca76d8c` actually did

Four collapsed bugs (all four the strategies the mission spec listed —
SMF runtime + interpreter outer + check helper + pure-Simple parser):

| Bug | Site | Strategy used |
|-----|------|---------------|
| 1. SMF mode: `rt_bdd_describe_end` `println!` bypassed Simple stdout buffer → `parse_test_output` saw empty → outer false-green | `src/compiler_rust/runtime/src/value/bdd_ffi.rs` (new `rt_bdd_snapshot_results()`, BDD_RESULTS Vec accessor) + `src/compiler_rust/driver/src/cli/test_runner/execution.rs` (`derive_counts_from_bdd_snapshot`, `run_test_file_smf_mode` queries it directly) | **Path B-equivalent**: bypass stdout entirely, read in-process BDD state |
| 2. Interpreter outer: static fast-path counted `it{}` blocks without running them | `src/compiler_rust/driver/src/cli/test_runner/runner.rs` (new `spec_has_assertions()` predicate; specs with `expect`/`check`/`check_msg`/`assert_*` route to slow path that calls `interpreter::get_test_results()`) | Slow-path-when-assertions, fast-path preserved for ~1% assertion-free specs |
| 3. `std.spec.check` interpreter helper only set Simple-side `current_test_error`, never tripped `BDD_EXPECT_FAILED` | `src/lib/nogc_sync_mut/spec.spl` lines 658-670, `src/lib/nogc_sync_mut/spec/__init__.spl` lines 27-38 (rerouted to `expect(condition).to_equal(true)`) | Reuse working matcher dispatch |
| 4. Pure-Simple parser only matched plural `examples`/`failures`, missed `1 example, 1 failure` | `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` lines 159-173 | Loosened substring match |

So the mission's "(A) parse-stdout vs (B) subprocess-exit" framing is moot —
the actual fix used a **third path: in-process BDD state snapshot** for SMF
mode, plus three independent helper-level fixes.

## Verification (run from worktree, after `cargo build --profile bootstrap -p simple-driver` green in 3m08s)

| Spec | Mode | Outer summary | Expected | Match? |
|------|------|---------------|----------|--------|
| `test/unit/compiler/r2_probe_fail_spec.spl` (deliberate fail: `expect(1).to_equal(2)`) | interpreter | `Passed: 0, Failed: 1, Some tests failed` | RED | ✓ |
| `test/unit/compiler/r2_probe_fail_spec.spl` | `--mode=smf` | `Passed: 0, Failed: 1, Some tests failed` | RED | ✓ |
| `test/unit/compiler/r2_lang_probe_spec.spl` (`check(true)` + `check(false)`) | interpreter | `Passed: 1, Failed: 1` | mixed | ✓ |
| `test/unit/compiler/r2_pending_helper_spec.spl` (passes) | interpreter | `Passed: 2, Failed: 0, All tests passed!` | GREEN | ✓ |

## Mission deliverable map

| Item | Status |
|------|--------|
| Implementation | Already landed in `f85ca76d8c` — not touched |
| Regression spec `test_runner_failure_propagation_spec.spl` | **Skipped** as redundant. `r2_probe_fail_spec.spl` (deliberate fail) and `r2_lang_probe_spec.spl` (mixed) already serve this purpose. Adding a duplicate would gold-plate. (Per advisor + CLAUDE.md "NEVER add unused code".) |
| `cargo build --profile bootstrap -p simple-driver` | Green, 3m08s |
| Smoke test passing fixture | `r2_pending_helper_spec.spl` → green ✓ |
| Smoke test failing fixture | `r2_probe_fail_spec.spl` interp + smf → red ✓ |
| Memory note updated | Already updated by author of `f85ca76d8c` (md5 `342df10125cf66d2acae6fedd7a9c375`); **not re-edited** |
| Wave-2 specs (`fixed_spec.spl`, `bignat_spec.spl`, `rsa_kat_spec.spl`, `integer_serde_spec.spl`, `fe25519_spec.spl`) | Not present in this worktree (`test/unit/lib/math/bignum/` doesn't exist here). They live in another wave's worktree; out of W-7 scope to verify here. No regression risk because no edits were made. |

## Build artifacts

- `src/compiler_rust/target/release/simple` (50934208 bytes, built 2026-04-25 22:18Z — post-fix)
- `src/compiler_rust/target/bootstrap/simple` (26690024 bytes)
- `execution.rs` md5: `abb48c3471276088630767715ffeacfe`
- `bdd_ffi.rs` md5: `496617a3919af93252900e9957d45d19`

## Why the mission spec was stale

Mission was authored against `27bc8e430a` (Phase 1) being the head of
test-runner work, but `f85ca76d8c` (Phase 2) landed roughly 7 hours later
on the same day. The dispatcher reused the Phase-1-era memory excerpt
without re-reading the latest note.

## Advisor notes

- Advisor call 1: confirmed mission was satisfied at dispatch and recommended
  not touching working files; recommended skipping the redundant new spec;
  recommended skipping bootstrap rebuild (test path uses release profile, not
  the deployed self-hosted binary — see memory note "Where bin/simple actually
  goes" section).
- Advisor call 2 (pre-done): pending.
