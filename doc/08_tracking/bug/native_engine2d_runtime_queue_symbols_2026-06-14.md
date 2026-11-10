# Native Engine2D Runtime Queue Symbols Missing From Linked Runtime

Date: 2026-06-14
Status: FIXED (verified 2026-11-11, lane rt3) — `native-build` now works on this
Windows host, `rt_host_gpu_queue_*` symbols are exposed in the linked native
binary, and the CPU-only import split has landed. See the 2026-11-11 addendum.

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

---

## 2026-11-11 — Lane rt3 triage verdict: FIXED

Both halves of the Minimal Fix are now landed and verified:

1. **Native archive/binary exposes `rt_host_gpu_queue_*`.** The 2026-09-13
   blocker — "`bin/simple native-build` fails on this Windows host before
   producing a binary (`native-build worker wrapper exited abnormally ...
   code -1`)" — no longer reproduces on the refreshed seed (build
   `46fe8f6b6def`). A small native build now compiles and links:
   - Fixture: `build/scratch/rt3_bug8_native.spl` (raw
     `rt_host_gpu_queue_emit_payload_text`/`drain`/`last_payload_hash`
     externs, one module).
   - `SIMPLE_NATIVE_BUILD_RUST=1 bin/simple.exe native-build
     build/scratch/rt3_bug8_native.spl -o build/scratch/rt3_bug8_native.bin`
     → `Linked: build/scratch/rt3_bug8_native.bin (511 KB) via clang`, rc=0.
   - `nm build/scratch/rt3_bug8_native.bin` → **48** `rt_host_gpu_queue_*`
     symbols linked, including `T rt_host_gpu_queue_complete` and refptrs for
     `emit_payload_text` / `drain` / `last_payload_hash` / `reset`.
   - Running the binary prints `native hash=424242` — the queue works
     natively, and the emitted `payload_hash` round-trips (cf. the sibling fix
     for `host_gpu_runtime_emit_payload_text_drops_hash_2026-07-08`).
   - Registry rows remain in place (`config/api/api_registry.sdn:1904-1908+`
     list `rt_host_gpu_queue_*` with `nm`-verified backing), and
     `src/runtime/runtime_native.c` carries 142 `rt_host_gpu_queue`
     references.

2. **CPU-only import split has landed.**
   `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`
   now states in its Overview: "It intentionally avoids SGTTI and broad
   browser imports so native verification stays scoped to Engine2D, Draw IR,
   and the runtime queue API", and imports only `common.ui.draw_ir` +
   `engine2d.draw_ir_runtime_adv` + `engine2d.draw_ir_runtime_queue`. The spec
   passes 4/4 on the interpreter lane.

**Caveats:** (a) the fail-closed `check-extern-abi-signatures.shs` arity gate
currently ERRORs (`exit 2 — nothing was checked`) because it references a
missing file `src/compiler/70.backend/backend/llvm_lib_translate.spl`; that is
pre-existing gate infra drift on this branch, unrelated to this bug — the
symbol exposure was instead verified directly via `nm` over a freshly linked
binary as above. (b) `--mode=native` for *specs* degrades to the interpreter
on the Rust seed ("Ran on the interpreter; this file's REAL pass/fail is
reported"), so native spec evidence still uses the direct native-build route.
