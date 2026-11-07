# Windows: native-build child JIT-loads the compiler closure from source (~4.9 GB / ~125 s before SCV admission); SCV inventory cold init is not the memory cost

- **ID:** `windows_scv_inventory_cold_init_memory_2026-11-07`
- **Status:** OPEN (re-scoped 2026-11-07 by lane w-scvmem)
- **Priority:** P2
- **Area:** `src/app/cli/native_build_main.spl` coordinator run from source by `bin/simple.exe` (not `src/app/compiler_entrypoint/inventory_events.spl`)
- **blocked_by:** phase3 self-hosted native-build deploy

## Re-scope (2026-11-07)

The original premise (cold SCV inventory init uses > 3.8 GB) is wrong.
`bin/simple.exe native-build` interprets/JITs the whole `native_build_main`
closure (src/compiler, src/lib, src/app; `[engine-demotion] reason=hybrid-interp-splice`)
and that load alone peaks at about 4.9 GB and takes about 125 s, BEFORE
SCV admission starts. The original probe (killed at 3818 MB after 44 s) was
still inside this load phase.

Binary: `bin/simple.exe` in a worktree at `fe52a1431e6` (origin/release/1.0.0, 2026-11-07).
Harness: PowerShell poll of `PeakWorkingSet64` every 250 ms, RSS timeline every 5 s.
Entry: two-line `test/scvmem_probe/hello.spl`; command
`bin/simple.exe native-build --backend cranelift --refresh-source-authority --entry-closure --entry test/scvmem_probe/hello.spl --runtime-bundle core-c-bootstrap --output test/scvmem_probe/hello.smf`
with `SIMPLE_BUILD_TRACE=1`.

| Run | Peak RSS | Wall | What it shows |
|---|---|---|---|
| run6, cold init, admission refused 1 ms after it started | 4867 MB | 126 s | No inventory work ran, same peak |
| run5, warm (no cold init) | 4898 MB | 129 s | Same peak without cold init |
| Both runs, at about 40 s | about 4.1 GB | — | Matches the original probe |
| run4, cold init that succeeded | 3.6–4.3 GB during admission | about 386 s admission | Cold init costs wall time, not RSS |
| `test --coverage` on a 1-spec dir | a child reached 5050 MB | hit the 600 s cap | Reproduces the reported shape |
| plain `test` on the same dir | 332 MB | 56 s | Without coverage the run stays small |

Disk: one cold-init run wrote about 295 MB to `<worktree>/build`, of which `build/scv` is 34 MB.

## Fix direction

A compiled native-build route or a precompiled worker, so the coordinator
does not load the compiler closure from source. Depends on the phase-3
self-hosted native-build deploy. Target unchanged: < 1 GB RSS and < 30 s for a
single-spec dir, pinned by a perf spec (a spec now would fail regardless of
inventory changes).

## Related

- `native_build_cold_init_admission_wall_386s_2026-11-07` (the real cold-init cost: wall time)
- `test_single_spec_dir_mcdc_manifest_contract_panic_2026-11-07`
- `coverage_test_flag_times_out_and_mcdc_no_probes_windows_2026-11-03`
- `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13`
- `scv_inventory_cold_rescan_935s_per_tree_change_2026-09-26`
