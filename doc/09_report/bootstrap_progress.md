# Bootstrap progress — 2026-11-07

Snapshot of per-platform bootstrap status on `release/1.0.0`. Each row cites
repo evidence. Anything not re-run on 2026-11-07 is marked **unverified**.

## Summary table

| Platform | Stage reached | Blockers | Landed PRs / commits | Evidence |
|---|---|---|---|---|
| **Linux arm64** (`aarch64-unknown-linux-gnu`) | Stage 2 compiled + admitted (Oct 2026); Stage 3 diagnostic build only, **no Stage 3 admission receipt**; no Stage 4 full CLI | Stage 3 planner admission (absolute source roots, fixed in diagnostic build, canonical re-run pending); `src/app/io/mod.spl` per-file 300 s timeout under Cranelift (retry recovers); historic `aot:lower_to_mir` malformed `HirType` (ZeroKind); `bin/release/aarch64-unknown-linux-gnu/simple` is still the Rust seed stopgap | #2756 (cranelift selector table), #2842 (named-variant pattern), `cbc65b90e49` (seed `--target` @when), `c374fcca687` (launcher probe), `f509393a354` (LLVM object format from target triple), `d2696f18a50` / `9df2886e412` / `0f3e8bf2041` (2026-11-05 ARM64 link leak + launcher guard specs) | `doc/08_tracking/bug/linux_aarch64_stage3_planner_absolute_source_roots_2026-10-09.md`, `doc/08_tracking/bug/linux_aarch64_cranelift_stage2_app_io_file_timeout_2026-10-02.md`, `doc/08_tracking/bug/bin_simple_is_seed_aarch64_stage3_blocked_2026-09-04.md`, `doc/08_tracking/bug/zerokind_is_a_corrupt_aggregate_2026-09-03.md` |
| **macOS arm64** (`aarch64-apple-darwin`) | Stage 2 run `s2y` ABORTED at `stage2-compiler-tests` (exit 1); Stage 3 never started | `compiler_cli_build` ~2 h with 1 worker (prior run timed out at 7200 s; profiling ongoing); 8 GiB memory reserve refuses Stage 3 (~5.7 GiB free on 24 GB host); Sep-18 full-CLI binary SEGVs on current tree; Stage 3 HIR RSS/SIGBUS; LLVM `i64`→`void` in `test_runner_build`; small-host per-file pool refusal (needs ≥30 GB) | This session: #7075, #7103, #7296, #7159, #7235, #7322, #7323, #7325, #7353, #7368, #7375, #7388, #7390, #7391, #7392, #7394, #7395, #7396, #7399, #7401, #7402, #7405, #7422, #7438, #7446, #7453, #7441, #7459 | `/private/tmp/boot4-out/s2y` (local, not in repo), `/private/tmp/s3-par2` (local) |

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
- **Stage 3 lane** (`/private/tmp/s3-par2`): never started. The 8 GiB memory
  reserve refused it with ~5.7 GiB free on the 24 GB host.
- **Full CLI binary:** the build deployed on Sep-18 SEGVs on the current tree.
  Because of that, the whole-tests, cross-compile (`x86_64-apple-darwin`,
  `riscv64-unknown-none`, `aarch64-unknown-simpleos`) and Phase 4 lanes
  produced **no verdicts**.
- **@cover fix:** 33 of 76 system specs fixed in commit `2fbe8e4d467`, on branch
  `work/system-spec-cover-annotations` (worktree `/private/tmp/cover-wt`).
  **Committed but not pushed.** It is blocked by the pre-push gate timeout and
  by Fable credits being exhausted.

## Open blockers (cross-platform)

1. Stage 3 HIR RSS growth / SIGBUS.
2. LLVM `i64`→`void` mismatch in `test_runner_build`.
3. Small-host per-file pool refusal: needs ≥30 GB RAM.
4. Linux arm64: Stage 3 admission receipt is missing, and the seed stopgap is
   still deployed.
