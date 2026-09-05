# Wave 1 audit results (measured 2026-08-18)

Aggregated from three read-only audits. Source of truth for the initial baselines
of the registries named in `plan.md`.

## A. Direct rt_* inventory

- **23,667** direct `rt_[a-z0-9_]*(` call-site lines in non-vendor `.spl` under `src/`.
- Buckets: src/lib 10,922 · src/compiler(+rust non-vendor) 4,249 · src/app 4,162 · src/os 3,665 · src/runtime 669.
- `extern` declarations naming rt_ symbols in .spl: 286 lines.
- Top files: `src/lib/common/torch/dyn_sffi_ops.spl` (189), `src/lib/nogc_async_mut/linalg/backend_ops.spl` (177), `src/runtime/simple_core/core_string.spl` (165), `src/lib/nogc_sync_mut/io/window_sffi.spl` (159), sffi/ffi codegen.spl (156/154).
- Declaration/provider seeds: `src/app/ffi_gen.specs/*.spl`, `src/compiler/90.tools/sffi_gen/specs/*.spl`, Rust `src/compiler_rust/native_all/src/lib.rs`, C `src/runtime/runtime_native.c`.
- **Alias archaeology verdict:** no rt_ import-alias mechanism was ever deleted. The history is a *codegen defect* thread: `079249904253` (root-cause import-alias defect), `652947404b44` (fix selective-import aliases in AOT/entry modules), `3f0acf071cf6` (static-method alias resolution); live victim list `scripts/check/import_alias_victims.txt` (92 lines, 2026-08-10). Only 3 `use … as _x` lines exist repo-wide, none rt_-related. ⇒ The sanctioned-alias design must first prove the alias mechanism is now sound in all lanes (the defect fixes above are the evidence trail to verify).
- **Checker gap confirmed:** 154 scripts mention rt_ but all are ABI/symbol-table gates (`check-rt-free-abi.shs`, jit manifest, lane divergence…). Nothing measures direct call-site counts. `check-no-direct-rt.shs` is greenfield.

## B. C inventory (src/runtime, vendor excluded)

- **107 files, 51,156 lines.** Areas: core runtime 12f/16,331L (runtime_native.c alone 11,139) · platform 17f/9,454 · process/thread 5f/6,374 · media 23f/5,409 · runtime self-tests 27f/3,870 · simd 4f/4,014 · memory 4f/2,438 · sqlite 2f/1,111 · openssl 3f/968 · wasm 1f/459 · bootstrap 6f/327 · time 2f/265 · mcp 1f/136.
- Top-10 classification: runtime_native.c, runtime.c, runtime_pool.c = runtime primitive (prime split/migration targets); runtime_process.c, runtime_thread.c, async_linux_epoll.c, async_windows.c, hosted_win32.c = platform shim; runtime_simd_dispatch.c = product algorithm; runtime_sdl2.c = third-party wrapper.
- Prior audits to import: `doc/08_tracking/feature/runtime_boundary_rt_cleanup_2026-06-21.md`, `doc/09_report/wm_wave0_core_c_runtime_capsule_2026-07-26.md`, `doc/09_report/jit_runtime_symbol_manifest_audit_2026-07-28.md`.
- No `c_migration_inventory.sdn` / `runtime_boundary_inventory.sdn` exists — greenfield.

## C. Duplicate binary helpers (merge map)

- None of `std.binary.inspect` / `std.spec.binary` / `std.spec.table` exist yet — all greenfield owners.
- ~25 copies of `bytes_to_hex`, ~40 of `hex_digit`/`byte_to_hex`, ~30 of `hex_char_value`, ~15 of `is_hex_digit`, 7+ hexdump implementations, 6 byte-identical `format_bytes`, 7+ markdown-table emitters.
- Dominant pattern: **wholesale cross-flavor copies** across `gc_async_mut` / `nogc_async_mut` / `nogc_sync_mut` trees (buffer/utilities, aws_sigv4, debug/remote/protocol ×4 trees, perf.spl ×3 identical).
- Merge map: `std.binary.inspect` ← hex/dump/format_bytes clusters; `std.spec.binary` ← seed from `src/lib/common/spec/evidence/format/binary_layout.spl`; `std.spec.table` ← seed from `src/app/test/bench/bench_report.spl` `_rows_to_md_table`. Full file lists in the audit transcript; first refactor tranche: the byte-identical ×3/×4 flavor copies (pure deletion, no behavior decisions).
