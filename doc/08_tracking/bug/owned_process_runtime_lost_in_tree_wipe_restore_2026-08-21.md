# Owned-process runtime lost in tree-wipe restore `ae55a746719`

- **Date:** 2026-08-21
- **Status:** FIXED (restored)
- **Last good content:** `f11bd8f0d6b` ("fix(jit): register struct-field runtime funcs + link owned-process C into seed runtime")
- **Surfaced by:** seed test sweep — `cargo test --release -p simple-compiler --lib owned_process`

## Symptom

The only surviving trace of the owned-process feature was the Rust unit test
`codegen::runtime_sffi::tests::owned_process_receipt_abi_is_registered_with_bounded_inputs`,
which failed at `compiler/src/codegen/runtime_sffi.rs:2219`:

```
panicked at compiler/src/codegen/runtime_sffi.rs:2219:67: owned process runtime spec
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 3748 filtered out
```

`spec_for("rt_process_run_owned_bounded_value")` returned `None` because every
producer of that symbol — the C implementation, its ABI header block, its
build wiring, its symbol-manifest entries, and its codegen spec — had been
deleted. The test is the only reason the loss was visible at all: nothing else
in the tree referenced the feature, so all seven push guards were green over a
tree with the whole feature missing. This is the same blind spot recorded in
`.claude/rules/vcs.md` — structural guards cannot see a coherent tree that has
simply lost a feature.

## What was lost (and how it was determined)

`git show f11bd8f0d6b --stat` enumerated the commit; `git ls-tree -r --name-only`
on both endpoints and `git diff f11bd8f0d6b HEAD -- <path>` (read in BOTH
directions, per the anti-revert protocol) separated genuine loss from later
legitimate edits.

| File | Loss |
|---|---|
| `src/runtime/runtime_process_owned.c` | whole file (1292 lines) deleted |
| `src/runtime/test/runtime_process_owned_selfcheck.c` | whole file deleted |
| `src/runtime/test/runtime_process_owned_adapter_selfcheck.c` | whole file deleted |
| `src/runtime/test/runtime_process_owned_nonunix_selfcheck.c` | whole file deleted |
| `src/runtime/runtime.h` | owned-process ABI block deleted: `RT_OWNED_PROCESS_{RECEIPT,CANCEL_RECEIPT,ASYNC}_VERSION`, `RtOwnedProcess{Receipt,CancelReceipt,TokenV2,StartReceiptV2,PollReceiptV2,ResultV2}`, and 11 `rt_process_owned_*` / `rt_process_run_owned_*` declarations |
| `src/compiler_rust/common/src/runtime_symbols.rs` | 4 manifest entries: `rt_process_owned_cancel`, `rt_process_owned_cancel_value`, `rt_process_owned_terminate`, `rt_process_run_owned_bounded_value` |
| `src/compiler_rust/runtime/build.rs` | `runtime_process_owned.c` dropped from `c_sources` and from `rerun-if-changed`; `SIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE` define dropped |
| `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` | `RuntimeFuncSpec::new("rt_process_run_owned_bounded_value", &[I64; 5], &[I64])` dropped (the sibling `rt_struct_alloc` / `rt_struct_receiver_valid` specs from the same commit SURVIVED — only the owned-process half was lost) |

Deliberately NOT restored (verified as later legitimate changes in the same
`build.rs` diff, unrelated to this feature): the removal of `runtime_ssr.c`
(the file no longer exists in the tree) and of `runtime_terminal.c` from
`c_sources`.

## Fix

Every piece above restored from `f11bd8f0d6b`, spliced rather than
whole-file-reverted for `runtime.h`, `build.rs`, `runtime_symbols.rs` and
`runtime_sffi.rs` so no later edit to those files was rewound.

## Evidence

`sh scripts/check/check-c-runtime-compiles-push.shs`

- before: `FAIL — 5 file(s) failed to compile ... (103 compiled clean, 2 skipped ...)`
  (4 of the 5 were the restored owned-process files, failing only because the
  `runtime.h` ABI block was still missing)
- after: `FAIL — 1 file(s) failed to compile: src/runtime/test/rt_browser_renderer_namespace_selfcheck.c (107 compiled clean, 2 skipped for unavailable external dependencies)`

All four restored files compile clean; the count of clean files rose 103 → 107.
The single remaining offender, `rt_browser_renderer_namespace_selfcheck.c`, is
an **untracked** file belonging to a concurrent session
(`browser_renderer_apply_namespaces` / `browser_renderer_drop_privileges` are
undeclared). It was confirmed failing independently of this change and is not
in scope here.

## Companion defect: `rt_thread_sleep` defined twice in the Stage4 core archive

Surfaced by the same sweep, via the Stage4 SQLite C-provider contract in
`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`.

Two definitions existed:

- `src/runtime/runtime_thread.c:441` — `void rt_thread_sleep(int64_t millis)`,
  the **canonical** one. `tools.rs:358-361` states it outright: *"Canonical
  OS-thread and closure-pool provider. runtime_thread.c owns both `rt_thread_*`
  and `rt_pool_*`"*, and it is unconditionally in the core-C input list.
- `src/runtime/runtime_native.c:538` — `SPL_CORE_C_WEAK void rt_thread_sleep(...)`,
  a one-line forward to `rt_sleep_ms`.

The weak fallback was never selectable: the only build list that contains
`runtime_native.c` (`build_c_runtime_library`, `tools.rs:344`) also contains
`runtime_thread.c`, and both are compiled with `-DSIMPLE_CORE_C_STANDALONE=1`,
so guarding on that macro would not have separated them either. `nm` reports a
weak `W` as *defined*, so `validate_stage4_cli_c_provider_archive`
(`tools.rs:1118-1122`, which fails any canonicalised symbol whose definition
`count != 1`) and the `"Stage4 core must own \`{core_symbol}\` exactly once"`
check at `tools.rs:1445` both saw two.

**Fix:** removed the redundant weak definition from `runtime_native.c`, leaving
a comment in its place explaining why it must not come back. The exported C API
is unchanged — `rt_thread_sleep` is still defined (once) by `runtime_thread.c`,
so no `rt_*` symbol is removed from the tree. The now-stale row
`rt_thread_sleep\truntime_native.c,runtime_thread.c` was dropped from
`scripts/check/runtime_symbol_lane_divergence_baseline.txt`, since a baseline
that no longer describes the tree is how a ratchet stops ratcheting.

## Related

- `doc/08_tracking/bug/vulkan_engine2d_native_jit_missing_rt_struct_receiver_valid_2026-08-12.md` — the bug `f11bd8f0d6b` originally fixed.
- `.claude/rules/vcs.md` § "Sync must never clobber" and the tree-wipe incident records.

## Measured evidence (cargo, `CARGO_TARGET_DIR=/mnt/data/.cargo-target-owned`)

**A — `cargo test --release -p simple-compiler --lib owned_process -j 4`**

- before: `test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 3748 filtered out; finished in 0.00s`
- after: `test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 3748 filtered out; finished in 0.00s`

**B — `cargo test --release -p simple-compiler --lib -j 4 -- stage4_cli_c_provider`**

Proved by reverting `runtime_native.c` alone and re-running (the duplicate
restored), then re-applying:

- with the duplicate present: `test result: FAILED. 5 passed; 1 failed; 0 ignored; 0 measured; 3743 filtered out; finished in 18.48s`, failing in
  `test_stage4_cli_c_providers_are_disjoint_from_current_core_c` with
  ``called `Result::unwrap()` on an `Err` value: "Stage4 archive core defines `rt_thread_sleep` 2 times"`` — the exact reported defect.
- with the fix: `test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 3743 filtered out; finished in 16.72s`

**Pre-existing, NOT caused by either change:**
`pipeline::native_project::tests::test_stage4_sqlite_provider_round_trips_core_strings`
fails with `stage4_sqlite_probe failed: status=exit status: 2 stdout="" stderr=""`
(`tests.rs:2745`). Verified by running it against the tree with my
`runtime_native.c` edit reverted — it fails identically
(`test result: FAILED. 0 passed; 1 failed ... finished in 13.59s`). This is a
linked-probe runtime failure, a different defect from the duplicate-symbol
contract failure, and is left unfixed and unclaimed here.
