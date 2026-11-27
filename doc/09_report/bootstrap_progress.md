# Bootstrap progress — 2026-11-07

Snapshot of per-platform bootstrap status on `release/1.0.0`. Each row cites
repo evidence. Anything not re-run on 2026-11-07 is marked **unverified**.

## Summary table

| Platform | Stage reached | Blockers | Landed PRs / commits | Evidence |
|---|---|---|---|---|
| **Linux arm64** (`aarch64-unknown-linux-gnu`) | Stage 2 compiled + admitted (Oct 2026); Stage 3 diagnostic build only, **no Stage 3 admission receipt**; no Stage 4 full CLI | Stage 3 planner admission (absolute source roots, fixed in diagnostic build, canonical re-run pending); `src/app/io/mod.spl` per-file 300 s timeout under Cranelift (retry recovers); historic `aot:lower_to_mir` malformed `HirType` (ZeroKind); `bin/release/aarch64-unknown-linux-gnu/simple` is still the Rust seed stopgap | #2756 (cranelift selector table), #2842 (named-variant pattern), `cbc65b90e49` (seed `--target` @when), `c374fcca687` (launcher probe), `f509393a354` (LLVM object format from target triple), `d2696f18a50` / `9df2886e412` / `0f3e8bf2041` (2026-11-05 ARM64 link leak + launcher guard specs) | `doc/08_tracking/bug/linux_aarch64_stage3_planner_absolute_source_roots_2026-10-09.md`, `doc/08_tracking/bug/linux_aarch64_cranelift_stage2_app_io_file_timeout_2026-10-02.md`, `doc/08_tracking/bug/bin_simple_is_seed_aarch64_stage3_blocked_2026-09-04.md`, `doc/08_tracking/bug/zerokind_is_a_corrupt_aggregate_2026-09-03.md` |
| **Windows x86_64** (`x86_64-pc-windows-gnu`, llvm-mingw) | Stage 3 leaf `s3_fable61` passes the gate (c01/c03/c07/fn1/hello/var); Stage 4 / phase-4 full-CLI link not yet produced | vb_mm1 native method lookup (fold `d05dc7079db` → leaf 63); C: disk < 15 GB blocks leaf 62 + stage2 rebuild #2; F3 runner 1 h limit (19 GB worker sawtooth, 595 s first object); Windows pre-push gate hang | #7315, #7329, #7357, #7376, #7378, #7385, #7393, #7410, #7457, #7483, #7506, #7541, `82eb75b12d4` | `C:/dev/p3new/s3new/fable_milestones.md` (local), `doc/08_tracking/bug/native_method_call_hir_lowering_invalid_array_handle_2026-11-07.md`, `doc/08_tracking/bug/stage2_mir_scoped_borrowed_trait_providers_dangling_copy_2026_11_07.md` |
| **macOS arm64** (`aarch64-apple-darwin`) | Stage 2 run `s2y` ABORTED at `stage2-compiler-tests` (exit 1); Stage 3 (s3-par2) RUNNING from s2y binary, 2 workers, in parse shards | `compiler_cli_build` timed out at 14400 s with 24/3095 modules staged (8-module codegen batches took 1688/1144/5210 s). **Root cause (profiled):** 43% of main-thread samples were in `reverse_reference_sorted_v1` vs ~0.5% in LLVM codegen. Every per-module/per-batch `build_cache.save()` rebuilt and sorted the whole-program reverse-reference receipt (modules x facts log facts). **#7649: fix landed, rerun pending** (intermediate saves write entries only; the final save publishes); 8 GiB memory reserve refuses Stage 3 (~5.7 GiB free on 24 GB host); Sep-18 full-CLI binary SEGVs on current tree; Stage 3 HIR RSS/SIGBUS; LLVM `i64`→`void` in `test_runner_build`; small-host per-file pool refusal (needs ≥30 GB) | This session: #7075, #7103, #7296, #7159, #7235, #7322, #7323, #7325, #7353, #7368, #7375, #7388, #7390, #7391, #7392, #7394, #7395, #7396, #7399, #7401, #7402, #7405, #7422, #7438, #7446, #7453, #7441, #7459, #7649 | `/private/tmp/boot4-out/s2y` (local, not in repo), `/private/tmp/s3-par2` (local) |

## Windows x86_64 detail (`x86_64-pc-windows-gnu`, llvm-mingw UCRT)

Driven from the Windows host (80 threads). The phase-3 leaf lane rebuilds
selected compiler modules with the newest stage3 compiler and relinks
`s3_fableNN.exe` with a 64 MiB stack. The milestone log is
`C:/dev/p3new/s3new/fable_milestones.md` (local, not in repo).

- **Stage 2:** the old frozen stage2 still builds stage3 leaves.
  - Rebuild #1 from current source (`stage2_new.exe`, 1,618 objs, rc=0) failed
    the c01 smoke with a native-build worker AV. Root cause:
    `borrowed_trait_providers` was copied inside a live MIR transient scope.
    Fixed by **#7541**.
  - Rebuild #2 failed on 1 file (`Array.fill_span`), because the seed predated
    `rt_array_fill_span`. A fresh cargo seed is built. The re-run is staged with
    the workaround-removal commit and is **waiting for disk** (it needs ≥15 GB
    free on C:).
- **Stage 3 leaves:**
  - `s3_fable57s`: the F3 test-runner stack overflow was fixed by #7357 (8 MiB
    mingw stack). It is the base for the phase-4 sweep.
  - `s3_fable59`: the full gate (c01/c03/c07/fn1/hello/var) passes, as do the
    fixtures s2var, f3r_b, inferarm1 and oj_plain/ifonly/match/ifvar. This
    **natively verifies** the `83c17508b4a` site, #7329 and #7393 (inferarm and
    methods_mir with the workarounds removed), and
    `native_mir_nested_array_index_push_av`.
  - `s3_fable60`: failed its target. `core_codegen` sealed-failed, so #7410 is
    not foldable on the old base.
  - `s3_fable61` (#7506, the `g_pending_defers` fix): the gate passes.
    **vb_mm1 is still COMPILE-FAIL** (`unresolved method call Custom::get`), but
    the invalid-handle rejections dropped to 0. The remaining root cause: the
    leaf base lacks `d05dc7079db`, the `rti` child-dict promotion. The fold
    `p63_vbmm1.diff` is ready.
  - Leaf 62 folds b961e59c064, 728ddb0170f, 5a45cad0d94 and #7528 (partial).
    It is **waiting for disk**.
- **Phase 4:** the full compiler/CLI is compiled in lanes on the stage3 leaf.
  - Groups F (`lower_type` AV) and G are fixed, and group I (the 83c site) is
    verified.
  - The open groups are the vb_mm1 method lookup (775 errors in q0023) and the
    q0019/q0021 memory-cap kills. The kills are caused by MIR sharding being
    disabled on stale leaves; the rerun with
    `SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=32` is staged.
  - There is no final link yet (no entry object).
- **Test runner (F3):** the crash sites (UAF 82eb75b12d4, stack, 83c) are
  fixed. On 59 the run hits the 1 h harness limit. One worker sawtooths up to
  19.4 GB, and the first object takes 595 s; both are filed as P1s.
- **Blockers:**
  1. C: disk (~6–12 GB free, while leaves and stage2 need ≥15 GB).
  2. vb_mm1 (the fold in leaf 63).
  3. The pre-push gate `push-private-import-baseline` hangs on Windows (the
     `/tmp` path at line 58), which blocks most lanes from pushing; a fix is in
     progress.
  4. Fable review credits are exhausted (Opus review is the fallback).
## Linux arm64 detail

- **Stage 1 (seed) + Stage 2:** pass. 2026-09-04 record: Stage 2 pure-Simple
  binary admitted (152 MB, reports `simple-bootstrap 1.0.0-rc.1`). 2026-10-09
  record: Stage 2 compiled (522 modules rebuilt, 688 cached) and passed.
- **Stage 3:** the planner rejected absolute source roots; the fix validated
  on 17 producer/verifier fixtures, but the record says plainly that the
  diagnostic build "is not a Stage 3 admission receipt". Full admission is
  pending a canonical-checkout re-run.
- **Stage 4 / deployed tool:** none. `bin/release/aarch64-unknown-linux-gnu/simple`
  is the Rust seed (bug record of 2026-09-04, still OPEN).
- **Unverified:** no Linux arm64 bootstrap was re-run for this report. The
  newest arm64 commits (2026-11-05) are link-leak and launcher-path fixes plus
  guard specs, not bootstrap receipts. Whether Stage 3 now admits on Linux
  arm64 is **unknown**.

## macOS arm64 detail (this session)

- **Stage 2 run s2y** (`/private/tmp/boot4-out/s2y`): ABORTED at
  `stage2-compiler-tests`, exit=1. `compiler_cli_build` takes about 2 h with 1
  worker. A prior run timed out at 7200 s. Profiling is ongoing.
- **Stage 3 lane** (`/private/tmp/s3-par2`): STARTED 2026-11-07 15:33 KST from the
  sanity-passing `s2y` Stage 2 binary (cranelift, `--threads 8`). Auto memory policy
  clamped to **2 parse-shard workers** (15.4 GB available, 8 GiB reserve, 3.8 GB
  worker budget). source_closure done (1606/1606 files); parse shards running, peak
  shard footprint 2.68 GB, swap steady ~2.0/3 GB. One shard exited early (outcome
  unknown). Next: restart on the HIR-memory fix when it lands.
- **Full CLI binary:** the build deployed on Sep-18 SEGVs on the current tree.
  Because of that, the whole-tests, cross-compile (`x86_64-apple-darwin`,
  `riscv64-unknown-none`, `aarch64-unknown-simpleos`) and Phase 4 lanes
  produced **no verdicts**.
- **@cover fix:** 33 of 76 system specs fixed in commit `2fbe8e4d467`, on branch
  `work/system-spec-cover-annotations` (worktree `/private/tmp/cover-wt`).
  **Committed but not pushed.** It is blocked by the pre-push gate timeout and
  by Fable credits being exhausted.

## Open blockers (cross-platform)

1. Stage 3 HIR RSS growth / SIGBUS. One contributing cause has been fixed in
   PR #7686 (2026-11-07). Phase 1's interface index leaked per-character text
   scratch, which added +2.72 GB before parse even started. On the macOS arm64
   full-CLI build, peak RSS before the fix was 7.45 GB at HIR module 1073 of
   the closure. The phase reproducer over the 3097-source closure dropped from
   3.37 GB to 1.60 GB, with byte-identical output. HIR itself still grows from
   6.18 GB to 7.1 GB over 1073 modules, so this blocker stays open. See
   `doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md`.
2. LLVM `i64`→`void` mismatch in `test_runner_build`.
3. Small-host per-file pool refusal: needs ≥30 GB RAM.
4. Linux arm64: Stage 3 admission receipt is missing, and the seed stopgap is
   still deployed.
