# Native Engine2D Runtime Queue Symbols Missing From Linked Runtime

Date: 2026-06-14
Status: Open

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
