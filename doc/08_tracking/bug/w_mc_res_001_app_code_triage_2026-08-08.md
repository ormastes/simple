# W-MC-RES-001 app-code triage — 2026-08-08

Scope: all `src/app/` + `src/os/` files containing an `rt_[a-z0-9_]*_(open|create|new|alloc|acquire|copy|clone|load)(` call
(56 candidate files), each run through the real checker
`compiler.semantics.lint.unwrapped_foreign_resource.check_unwrapped_foreign_resource`
(interpreter harness, `SIMPLE_EXECUTION_MODE=interpreter`). 6 findings total; 50 files clean.

Classes: **TRUE** = real handle escapes unwrapped where a wrapper exists/should ·
**FALSE** = checker misread (managed lifecycle or non-handle) ·
**BOUNDARY** = the fn is itself the FFI boundary (correct fix per REQ-MC-023 is the
`@unsafe(reason: ..., capabilities: [ffi])` decorator, as applied in
`src/compiler/70.backend/sffi_minimal.spl`).

| # | File:line | Call | Class | Evidence |
|---|-----------|------|-------|----------|
| 1 | `src/app/debug/remote/dwarf.spl:116` | `rt_dwarf_load(path)` in `fn dwarf_load` | TRUE | A managed wrapper already exists earlier in the same file (struct holding `handle`/`loaded`, freeing via `rt_dwarf_free` on close); the "standalone convenience" forwarder re-exposes the raw handle beside that wrapper — either route callers through the wrapper or decorate the load/free pair as an explicit `@unsafe` boundary. |
| 2 | `src/app/debug/native_agent.spl:71` | `self.dwarf_handle = rt_dwarf_load(program_path)` in `attach()` | FALSE | `NativeBackend` IS the managing wrapper: handle stored in a field, guarded (`== 0` error path), and freed in `detach()` (lines 81–83 `rt_dwarf_free` + reset to 0); the checker cannot see field-based ownership. |
| 3 | `src/app/io/feature_registry.spl:36` | `rt_cuda_mem_alloc(size)` in `fn cuda_port_alloc` | BOUNDARY | Adapter fn injected as `alloc_fn` into the `GpuComputePort` function table, paired with `cuda_port_free` (`rt_cuda_mem_free`); the port abstraction is the wrapper and this fn is its FFI edge. |
| 4 | `src/app/ui.web/ws_handler.spl:25` | `rt_sha1_new()` in `fn ui_web_ws_sha1_new` | BOUNDARY | Module is a thin extern-adapter shim: one-line forwarders for the full `sha1` handle lifecycle (`new`/`write`/`finish_base64`/`free`); its whole purpose is exposing the raw handle to the WS-handshake caller. |
| 5 | `src/app/ui.web/server.spl:59` | `rt_tls_server_create(port, cert_path, key_path)` in `fn web_server_tls_create` | BOUNDARY | One-line forwarder over the SFFI import `std.nogc_sync_mut.io.tls_sffi.rt_tls_server_create`; returns a server-lifetime listener handle — the fn is the boundary adapter, no intermediate wrapper tier exists in this app. |
| 6 | `src/os/drivers/audio/hda_dma_resources.spl:91` | tail return `resources` from `fn hda_dma_resources_create` (`rt_alloc` + `rt_dma_alloc` handles) | BOUNDARY | Kernel-driver resource-table constructor: every error path calls `hda_dma_resources_destroy` (which `rt_dma_free`s each handle and `rt_free`s the table), and the paired destroy fn is the documented release path; MDSOC kernel tier has no RAII wrapper layer to wrap into. |

## Summary
- TRUE: 1 (dwarf.spl convenience forwarder duplicating an existing wrapper)
- FALSE: 1 (native_agent.spl — field-managed lifecycle, checker blind spot; matches the metadata-gap family in `w_mc_res_001_overfires_verb_only_heuristic_2026-08-07.md`)
- BOUNDARY: 4 (feature_registry, ws_handler, ui.web/server, hda_dma_resources — candidates for the `@unsafe(..., capabilities: [ffi])` decorator)

No fixes applied here — report only. The three compiler-side TRUE positives in
`src/compiler/70.backend/sffi_minimal.spl` (lines 178/181/253) were fixed the same day
with `@unsafe` boundary decorators (verified 3 → 0 findings via the interpreter harness).
