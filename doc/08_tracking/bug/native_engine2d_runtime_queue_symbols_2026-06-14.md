# Native Engine2D Runtime Queue Symbols Missing From Linked Runtime

Date: 2026-06-14
Status (2026-07-18): runtime SFFI registration and focused ABI regression are
implemented; exact interpreter/native queue parity is scheduled on every
hosted LLVM/Cranelift matrix leg and FreeBSD, with first execution pending.

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

## Historical minimal fix

The original remediation was to regenerate or rebuild the selected native runtime archive from the current
`src/runtime/runtime_native.c`, then add `rt_host_gpu_queue_*` to the simple-core
required-symbol check. After that, split a CPU-only Engine2D/Draw IR import path
so the runtime queue spec does not drag unrelated backend SFFI/WFFI imports.

## Resolution status (2026-07-18)

The queue facade is C-owned and runtime selection rejects archives that do not
provide its required symbols. The missing
`rt_host_gpu_queue_emit_payload_text` SFFI entry is now registered with its
six-argument pointer-compatible ABI and covered by a focused Rust regression.
`scripts/check/check-native-runtime-queue.shs` now incrementally builds the
queue probe with the host-GPU runtime bundle, using flagless default
LLVM or explicit Cranelift, then requires byte-identical interpreter/native
output plus the backend handle, payload hash/text, and overflow oracles. Each
interpreter/build/run stage is timeout-bounded, and its incremental cache is
namespaced by compiler checksum. The
probe also traverses the production Draw IR SDN producer and dispatch helper.
That path no longer calls unsupported bootstrap `.join()` on a dynamic text
array; both SDN emitters share a small pure-Simple newline loop instead. The
Linux, macOS arm64/x64, Windows x64, and FreeBSD x86_64 matrices schedule the
gate. First staged execution remains required before the bug is fully verified;
cross-target object checks cannot prove this host runtime-link defect.
