# Native Engine2D Runtime Queue Symbols Missing From Linked Runtime

Date: 2026-06-14
Status: Open (re-triaged 2026-09-13 — see the note at the end of this file)

## Symptom

Native execution of the focused Engine2D Draw IR runtime queue spec can crash or
fail to link even though interpreter coverage passes.

## Evidence

`src/runtime/runtime_native.c` defines the `rt_host_gpu_queue_*` C runtime
entrypoints and the compiler symbol tables know about them, but the native
runtime object/archive used by the spec did not expose `rt_host_gpu_*` symbols
during the audit. The same audit also found broad Engine2D imports pulling SFFI
and WFFI backend surfaces into a CPU-only runtime queue spec.

## Impact

This blocks using native `draw_ir_runtime_queue_spec` as production evidence for
Engine2D runtime queue emission. Interpreter evidence and lower-level runtime
queue evidence still pass, but native Engine2D queue coverage is not complete.

## Minimal Fix

Regenerate or rebuild the selected native runtime archive from the current
`src/runtime/runtime_native.c`, then add `rt_host_gpu_queue_*` to the simple-core
required-symbol check. After that, split a CPU-only Engine2D/Draw IR import path
so the runtime queue spec does not drag unrelated backend SFFI/WFFI imports.

## Triage 2026-09-13 — LEFT OPEN (half done; the native half is unverifiable here)

- **measured**: the registry half of the Minimal Fix has landed. `rt_host_gpu_queue_*` appears 143 times in `src/runtime/runtime_native.c` and is now declared in the API registry — e.g. `config/api/api_registry.sdn:1904-1906` lists `rt_host_gpu_queue_complete`, `rt_host_gpu_queue_completed_count`, and `rt_host_gpu_queue_complete_packet`.
- **inferred**: what the registry rows do NOT establish is the reported symptom, which was about the linked native ARCHIVE not exposing those symbols. Confirming that needs `nm` over a freshly built `libsimple_runtime.a` plus a native run of `draw_ir_runtime_queue_spec`.
- **measured**: neither is possible here — `bin/simple native-build` fails on this Windows host before producing a binary (`native-build worker wrapper exited abnormally ... code -1`).
- **inferred**: the second half of the Minimal Fix — splitting a CPU-only Engine2D/Draw IR import path so the queue spec stops dragging SFFI/WFFI backend surfaces in — shows no sign of having been done.
- Verdict: OPEN.
