# Second MirCallOrigin.Unknown producer: stage3 codegen abort on driver_hir_archive_schedule_v1 (2026-11-13)

**Status:** OPEN (observed 2026-11-13 02:06 KST, aarch64 Linux, s3gen lane, pinned df719eff44cf)
**Area:** compiler / MIR callable authority -> LLVM core_codegen
**Related:** `unknown_call_origin_panics_codegen_worker_2026-11-12.md` (same panic, different
producer — its HIR scoping trigger 168a972855a IS an ancestor of the pinned snapshot, so this
is a NEW producer, not a reopen of run 13).

## Symptom

Stage 3 self-build (stage2-admitted compiler from pinned `df719eff44cf` building the same
1626-module closure) reached staged codegen batch 35 with 7 uncached modules:

```
[build] phase=native_compile ... done=1 total=8 ... current=compiler.driver.cache.driver_hir_archive_schedule_v1
[NATIVE] codegen: 7 uncached module(s), concurrency=1 (serial lane in this process: backend session owns codegen)
MIR call target lacks proven source/runtime/foreign origin
```

then SIGABRT (signal 6). The aborting process was
`stage2-admitted/simple run src/app/cli/native_build_worker.spl` (pid 1092666,
~36 GiB RSS at crash — memory was NOT the cause; cap 54525952 KiB and the 48 GiB
runtime reserve were both satisfied at crash time).

`mir_call_origin_uses_local_symbols` (`src/compiler/50.mir/mir_instruction_support.spl:289`)
panicked on `MirCallOrigin.Unknown` — the same fail-stop shape as run 13. The MIR verify pass
over the same 8-module batch reported `fatal=0` (MIRV-006b=1650, MIRV-004c=31 non-fatal), so
verify still tolerates Unknown and the panic fires only inside the backend.

## Why this is a new producer

- Pinned snapshot `df719eff44cf` (2026-11-12 20:28, PR #8650 chase fix) CONTAINS
  `168a972855a` (2026-11-12 13:30, "fix(hir): stop enum payload fields shadowing callables
  (run-13 Unknown call origin abort)") and its pin `782e0f9e056`.
- The run-13 trigger was `app.office.word.word_app` (enum UIEvent payload shadowing
  `common.ui.builder.button`). This crash is in
  `compiler.driver.cache.driver_hir_archive_schedule_v1` — a compiler-internal module with no
  UI enums — so the scoping-leak family does not explain it.

## Leading hypothesis

`provider_callable_call_origin_v1`
(`src/compiler/50.mir/_MirLowering/provider_metadata.spl:214`) returns `Unknown` when the
`(defining_module, name)` key is ABSENT from `callable_text_value_abi` — "an absent row is not
an extern or a safe local-call contract". The registry is built from defining HirFunction
metadata; a lookup/build key mismatch (canonical-fold chase-family shape: std./lib. alias vs
canonical bucket) would silently drop the row and produce Unknown at codegen time. The
stage2-admitted binary built this same closure fine when IT was built by the seed; the
divergence appears only when the stage2 binary compiles the tree — consistent with a
miscompiled key/fold path or a data-dependent registry gap.

Alternative: a second scoping/shadowing path not covered by 168a972855a (it fixed enum
struct-variant payload fields only; class fields, match bindings, or closure params could
still shadow a callable named in driver_hir_archive_schedule_v1).

## Evidence anchors

- Crash dump: `/var/crash/_home_yoon_dev_simple-boot-s3gen-20261112_build_bootstrap_pinned-src_pinned-df719eff44cf_build_bootstrap-s3gen_stage3_aarch64-unknown-linux-gnu_stage2-admitted_simple.1000.crash` (SIGABRT, no symbols).
- Native-build log: `build/bootstrap-s3gen/logs/aarch64-unknown-linux-gnu/stage3-native-build.log` line ~293501 (error) with `mir_verify: modules=8 ... fatal=0` immediately before `aot:native_session_open`.
- Lane: attempt I #2 (01:17 KST relaunch); wrapper wedged after the crash (systemd-run --wait did not reap for ~20 min); operator-terminated, fail-closed lock verified holder-dead and cleared.

## Next

1. Repro cheap: `$P/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple native-build
   src/compiler/driver/cache/driver_hir_archive_schedule_v1.spl --entry-closure --threads 1
   --cache-dir <fresh>` from the pinned tree (run-13 repro pattern; expect ~15 s abort).
2. Name the callee: rerun with codegen-worker stderr captured, or add the callee name to the
   panic message (small, landable fix).
3. Fix the producer (registry key fold or second scoping path) at release/1.0.0 tip; the
   per-unit-error robustness work stays tracked in
   `unknown_call_origin_panics_codegen_worker_2026-11-12.md`.
4. New pinned snapshot after the fix; stage3 attempt J from the new tip (146 commits have
   landed on release/1.0.0 since df719eff44cf).

## Correction (2026-11-13 ~03:20 KST): actual panic module is likely driver_pipeline_lowering

The `current=` build line lags batch logging. Cache forensics on
stage3-native-cache prove the real order: aot objects were published at
02:05:51-53 for batch-35 modules idx 1 (driver_hir_archive_schedule_v1),
2 (native_staged_codegen), 3 (go_to_end), 5 (driver_aot_codegen_outputs),
6 (driver_aot_smf_output); idx 4 (retained_source_traversal_v1, structs-only,
no functions) emits no aot. The first module attempted after 02:05:53 with NO
aot and NO build_cache row is therefore **idx 7,
compiler.driver.driver_pipeline_lowering** (functions=48), with idx 8
(driver_pipeline_execution, functions=2) next. driver_pipeline_lowering is a
1771-line module dense in transient/sffi machinery (transient_owner_sffi
wrappers, sha256_text, std.-alias imports) -- consistent with the registry
origin-miss hypothesis. J lane (tip pin incl. #8703 named panic) will confirm
the callee name definitively.
