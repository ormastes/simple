# P4 per-file unit memory blowup, idle provider waits, and borrowed-text copies

- **Date:** 2026-11-25
- **Area:** compiler driver (`80.driver`, `00.common`), MIR lowering (`50.mir`)
- **Severity:** release blocker (Stage 4 CLI could not build within the enforced 18 GiB footprint cap on the 24 GiB macOS arm64 RC host)
- **Status:** fixed across 6 coordinated fixes (`A`, `A2`, `B`, `C`, `E`, `F`); verified end-to-end with `manual-successor-v8`

## Symptoms

The sixth Stage 4 (`P4`) release-CLI attempt on `release/1.0.0` stopped at the enforced 18 GiB physical-footprint cap (`exit 88`, `peak_single_phys_footprint_kib=17159614`) after claiming only 162 of 4,173 modules in five 32-module units (~4–4.5 min/unit).

Subsequent diagnosis also uncovered a severe memory regression introduced on `release/1.0.0` by commit `3b19ef44f43` (`fix(mir): preserve embedded NULs in native text slice methods`) when lowered text methods received borrowed `RtCoreString.data` pointers (`s->data`), inflating both coordinator closure walk (`1.8 -> 3.6 GiB` footprint with `3.2 GiB` dirty `MALLOC_SMALL (empty)`) and single-process HIR cache reloads (`+10 GiB` in `driver_hir_cache`).

## Root causes and fixes

1. **Fix A — Whole-inventory native interface index in every unit (`src/compiler/80.driver/driver_source_pipeline_loading.spl`, `driver_source_parse_streaming.spl`):**
   Every unit child built `native_source_interface_index` across all 7,086 inventoried files during `load_sources`, adding ~44.5M mallocs and pushing `load_sources` to `6.9-7.5 GiB` even though each unit compiles `<= 32` targets. Unit children on the streaming route now skip the phase-1 whole-inventory index and build a unit-scoped index (`install_unit_interface_index_v1`) covering only MIR targets, advice roots, and their direct import targets after surfaces freeze.

2. **Fix A2 — Whole-inventory retained input fact snapshots (`src/compiler/80.driver/cache/native_module_input_fact_snapshots.spl`, `driver_source_parse_streaming.spl`):**
   `native_module_input_fact_snapshots_v1` indexed all 4,163+ surfaces in every unit instead of only `root_indices`. Added `native_module_input_fact_snapshots_for_modules_v1` so unit children retain snapshots only for their unit's target modules, producing bit-identical witnesses.

3. **Fix B — Idle 60 s provider settle wait in single-owner unit pools (`src/compiler/80.driver/driver_hir_cache.spl`):**
   With `--threads=1` (`owner 0/1@0`), no sibling worker can publish an unclaimed provider sidecar, so `hir_shard_provider_settle_wait_v1` slept the full `SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS` budget (60 s) per unit. Added `hir_unit_owner_pool_size_v1(owner) == 1` short-circuit returning immediately; multi-owner pools keep the existing wait.

4. **Fix C — Long-lived native fingerprint/interface string retention (`src/compiler/80.driver/driver_aot_native_output.spl`):**
   Moved per-file `driver_native_source_interface_text` construction and final `rows.join("\n")` hashing into `rt_transient_scope_*` blocks (`_driver_native_source_interface_metrics_v1`, `_driver_native_fingerprint_rows_hash_v1`), saving `~1.83 GiB` during phase-2 unit metadata hashing.

5. **Fix E — Allocation-heavy visibility manifest path checks (`src/compiler/00.common/cache/visibility_manifest_read_v1.spl`):**
   Replaced character-by-character `.split()` / `.char_at()` string allocations in `visibility_manifest_path_valid_v1` and `visibility_manifest_parent_v1` with zero-allocation ASCII byte scans (`byte_at`, `substring` slice). Eliminated ~3.3M coordinator allocations and sped up the closure walk by ~25% (`63.2s -> 50.1s`).

6. **Fix F — Zero-copy `RtCoreString` owner recovery in `ensure_tagged_str` (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`):**
   `file_read_nullable` and `Result<text, _>` unwraps return borrowed `RtCoreString.data` pointers (`s->data`) via `rt_interp_cstr`. After `3b19ef44f43` routed `.substring()`/`.slice()` through `lower_text_slice_v1` -> `ensure_tagged_str`, `ensure_tagged_str` only tested `original_word != rt_interp_cstr(original_word)`, which is false for borrowed `s->data` pointers, causing every `.substring()`, `.contains()`, `.starts_with()`, `.ends_with()`, and `.split()` on loaded source buffers to call `rt_string_new(s->data, rt_string_len(s->data))` and copy the entire 10–150 KB file per line. Added the `box_text_identity_v1`-style owner-recovery probe inside `text_box_raw` (`(word - 16) | 1` checked safely via existing `rt_string_data`), recovering the owning `RtCoreString*` with zero allocations.

Note on excluded candidate (Fix D): Wrapping `_pp_preprocess_conditionals` in `driver_entry_closure_core.spl` inside a transient scope was tested and explicitly rejected because `_pp_preprocess_conditionals` interns strings into global `pp_strip_memo_log` / `pp_strip_memo_count` dictionaries (creating a UAF risk; the outer coordinator closure loop already owns transient scopes safely).

Note on closure count (`4167 -> 4157` / `4173 -> 4163`): Pre-`3b19ef44f43` `v6` `.substring()` returned plain `SPL_MALLOC` `char*`, causing `scan_line.contains("\"\"\"")` in `driver_entry_closure_core.spl` to miss `"""` docstrings and falsely import `std.spec` / `testing.mock` from docstring examples (`src/lib/nogc_sync_mut/spec/engine_probe.spl:42`). Post-`3b19ef44f43` + Fix F properly skips docstrings (`selected=4157` probe / `4163` P4 build).

## Verification evidence (`manual-successor-v5` -> `v6` -> `v7` -> `v8`)

2-unit `P4` diagnostic benchmark (`SIMPLE_FILE_WORKER_BATCH=32`, `/tmp/simple-rc-build-20261122/p4-diag-unitmem-20261125/`):

| Producer | Coordinator peak footprint | Probe `MALLOC_SMALL (empty)` dirty | Unit 1 peak footprint | Unit 2 peak footprint | Unit 2 wall time |
|---|---|---|---|---|---|
| `v5` (baseline) | ~1.8 GiB | — | ~12 GiB | `12.12 GiB` | `158.4 s` |
| `v6` (Fixes A+B) | `1.85 GiB` | `180.8 MiB` (`63.2 s`) | `10.82 GiB` | `10.89 GiB` | `84.9 s` |
| `v7` (pre-Fix F) | `3.96 GiB` | `3.2 GiB` (`47.4 s`) | `12.53 GiB` | `11.56 GiB` | `83.8 s` |
| **`v8` (Fixes A+A2+B+C+E+F)** | **`1.64 GiB`** | **`152.9 MiB` (`50.1 s`)** | **`7.76 GiB`** | **`9.57 GiB`** | **`83.4 s`** |

`run6-v8` tree peak: `peak_phys_footprint_kib=11440547` (`10.91 GiB` < `18874368 KiB` cap), 64/64 modules `PASS`.
