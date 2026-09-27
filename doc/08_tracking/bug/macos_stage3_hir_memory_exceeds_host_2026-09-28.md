# macOS Stage 3: HIR memory growth exceeds what a 24 GB host can hold

Status: open, 2026-09-28. Host: M4 mac, 24 GB RAM, aarch64-apple-darwin.
Tree: `origin/main` with #1785, #1792, #1807, #1816, #1823.

## Command

1. Stage 2 (admitted, planner receipt produced):
   `bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --mode=dynload --jobs=10 --produce-stage3-receipt=verify-landed-compiler-fix`
2. Stage 3:
   `bootstrap-from-scratch.sh --resume-stage3-from-admitted=<out> --bootstrap-receipt=<receipt>`
   with `SIMPLE_NATIVE_BUILD_THREADS=10` and `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.

## Measurements

Both Stage 3 attempts were killed by the Darwin process-tree RSS watchdog while
still in HIR lowering (`phase3:hir`). Neither reached MIR or codegen.

| cap | peak RSS | wall time | progress at kill |
|---|---|---|---|
| 6 GB (5,859,375 KiB) | 5,859,408 KiB | ~30 min | in `driver_hir_pipeline_lowering.spl` |
| 7 GB (6,835,937 KiB, owner decision, #1823) | 6,867,184 KiB | ~25 min | 286 HIR files done, at `src/lib/nogc_sync_mut/sffi/platform.spl` |

- One compiler process carries almost all of the RSS: 1.6 GB at 13 min, at
  ~100% CPU. The thread count is not the multiplier.
- For comparison, Stage 2 compiled about 922 units. Linear extrapolation from
  286 files at 6.9 GB gives about 20 GB+ for Stage 3.
- This matches FreeBSD, which reached 26–28 GiB with 8 threads
  (`stage3_scv_inventory_noncanonical_and_stage2_struct_push_segv_2026-09-20.md`).

## Impact

The macOS bootstrap is verified through Stage 2 admission. Stage 3 cannot
finish on a 24 GB Mac under any cap the host can back. Stage 4 and deploy are
unreachable.

Owner decision (2026-09-28): record the gap and stop, rather than run
uncapped or single-threaded into swap.

## Next

This is compiler work, not a bootstrap-script change: find what HIR lowering
retains across files (per-file HIR, symbol tables, or module caches kept for
the whole closure) and bound it. Re-measure on this host afterwards.

Related:
- `macos_stage2_compiler_cli_build_host_gpu_link_2026-09-27.md` (the Stage 2
  compiler-test gap)
- `macos_scv_inventory_scratch_retention_2026-09-21.md`
