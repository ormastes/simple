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

## Update 2026-08-08 — the one TRUE finding is fixed; a mirror of it is NOT

`src/app/debug/remote/dwarf.spl:116` (the single TRUE finding above) is
**resolved**: the standalone `fn dwarf_load` convenience forwarder was
deleted. It was a pure duplicate of the managed `DwarfInfo.load` wrapper in
the same file, and a repo-wide sweep for `dwarf_load(` found only `fn`
definitions and build/worktree snapshots — never a call site. The module's
only importer (`src/app/debug/remote/feature/register_gdb.spl:11`) imports
`DwarfInfo` alone, so the deletion breaks nothing. Checker evidence:
that file goes `COUNT=1 (line_num=116)` -> `COUNT=0`. No `@unsafe` was used
— this was a real leak, not a boundary.

**Still open — a byte-near-identical mirror carries the same leak:**
`src/lib/nogc_sync_mut/debug/remote/dwarf.spl` has the same
`fn dwarf_load(path) -> i64: rt_dwarf_load(path)` returning a bare handle.
It is *more* reachable than the copy that was fixed, because it is public
API rather than a file-local convenience:

```
src/lib/nogc_sync_mut/debug/remote/__init__.spl:8   export dwarf_load, dwarf_free
src/lib/nogc_async_mut/debug/remote/dwarf.spl:8     use ... dwarf_load ...
src/lib/nogc_async_mut/debug/remote/__init__.spl:8  export dwarf_load, dwarf_free
src/lib/nogc_async_mut/sffi/debug.spl:20            use ... dwarf_load ...
```

So removing it is not the same one-line deletion: it retires a re-exported
symbol across two runtime tiers and five files. The sweep found no actual
CALL site anywhere in `src/` or `test/` — the whole chain appears to be dead
public surface — but "no caller today" is not the same as "safe to remove
from a published tier boundary", and an unresolved `use` only WARNs here
(fail-open), so a mistake would be silent rather than loud.

**Unblock condition:** confirm the four re-export/import sites above are the
complete set (they were found by grep, not by a resolver), then delete the
mirror's `fn dwarf_load` together with all four references in one change,
and re-run the checker over the mirror to confirm `COUNT=1 -> COUNT=0`.
Deliberately not done in the same pass as the app-side fix, to keep a
public-API retirement from riding along inside a leak fix.

**One drift correction to the table above:** the
`src/os/drivers/audio/hda_dma_resources.spl` finding is now at **line 92**,
not 91 — the file shifted by one line since the triage. Same single finding,
same BOUNDARY class. All five non-TRUE findings re-verified unchanged.

## Re-verification 2026-08-17

```
$ grep -n "dwarf_load\|fn dwarf_free\|deliberately no standalone" src/app/debug/remote/dwarf.spl
6:use std.sffi.debug.{rt_dwarf_load, rt_dwarf_free, rt_dwarf_addr_to_line,
21:        val h = rt_dwarf_load(path)
114:# There is deliberately no standalone `dwarf_load` here: acquiring a DWARF
117:# forwarder returning the raw `rt_dwarf_load` handle would let it escape
121:fn dwarf_free(handle: i64):
```

Confirmed: the standalone `fn dwarf_load` forwarder at the app-side
`src/app/debug/remote/dwarf.spl` is gone — line ~116 is now an explanatory
comment documenting its deliberate absence, matching the doc's own
2026-08-08 "Update" section. **This session's row description's evidence
quote ("dwarf.spl:116 rt_dwarf_load forwarder still present") is STALE —
the file content contradicts it.**

**Classification: ALREADY-FIXED-CLOSED** for the app-side TRUE finding (the
only one assigned in scope here, `src/app/**`). The doc's own "Still open"
mirror concern (`src/lib/nogc_sync_mut/debug/remote/dwarf.spl`) is a
`src/lib/**` file outside this session's scope lock and is left untouched;
that sub-issue remains as the doc describes it. No source changes made (fix
was already applied in a prior session). Status for the app-side TRUE
finding: RESOLVED, re-confirmed by source inspection.
