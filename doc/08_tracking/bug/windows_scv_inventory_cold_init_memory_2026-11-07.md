# Windows: SCV cold inventory init exceeds 3.8 GB RSS and 5 min CPU

- **ID:** `windows_scv_inventory_cold_init_memory_2026-11-07`
- **Status:** OPEN
- **Priority:** P2
- **Area:** `src/app/compiler_entrypoint/inventory_events.spl` (same site as `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13`)

## Symptom

Windows cold SCV inventory init on a single-spec directory exceeds 3.8 GB RSS
and 5 min CPU (probe killed by PID at 3818 MB after 44 s). This blocks
`bin/simple.exe test` (and `--coverage`) on Windows, because the test runner's
native-build wrapper sets `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.

## Target

- < 1 GB RSS and < 30 s wall for cold init of a single-spec directory.
- A perf spec pinning both bounds (RSS and wall) so regressions fail.

## Related

- `coverage_test_flag_times_out_and_mcdc_no_probes_windows_2026-11-03` (split out of this row; keeps the original evidence)
- `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13` (wall-time of the untracked walk; same code site)
- `scv_inventory_cold_rescan_935s_per_tree_change_2026-09-26`
