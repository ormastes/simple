# native-build cold-init SCV admission takes ~386 s even for a hello entry

- **ID:** `native_build_cold_init_admission_wall_386s_2026-11-07`
- **Status:** OPEN
- **Priority:** P2 (perf)
- **Area:** `src/app/compiler_entrypoint/source_authority.spl` (`compiler_source_authority_acquire_v1`), `src/app/compiler_entrypoint/inventory_events.spl`

## Symptom

With `SIMPLE_SCV_INVENTORY_COLD_INIT=1`, admission for a two-line
`test/scvmem_probe/hello.spl` took about 386 s (build-trace `+0ms coordinator:admission`
-> `+386582ms coordinator:worker:select`), Windows, `bin/simple.exe` at `fe52a1431e6`.
RSS during admission stayed 3.6–4.3 GB, below the ~4.9 GB load peak tracked in
`windows_scv_inventory_cold_init_memory_2026-11-07`. About 295 MB written to `build/`
(34 MB in `build/scv`).

Cold init always widens `inventory_roots` to `src` + `test` + `examples/10_tooling`
and the selectors for a hello entry are `src/app,src/lib,src/compiler,src/os,src/plugins,...`,
so every file in those trees is digested under the interpreter.

## Expected

Scope cold-init digests to the entry's closure, or cache them per root, so a
single-entry cold init is bounded (target well under 30 s).
