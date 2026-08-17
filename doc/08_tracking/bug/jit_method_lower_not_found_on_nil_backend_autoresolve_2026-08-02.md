# JIT: "method lower not found on nil" during engine2d backend auto-resolution

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Date:** 2026-08-02 · **Severity:** medium · **Area:** Cranelift JIT method dispatch / engine2d backend resolve

## Symptom

Running a program that triggers engine2d `"auto"` backend resolution through
`bin/simple run` (Cranelift JIT engine) dies with
`method lower not found on nil` inside the resolution path. The same code is
correct under the tree-walk interpreter
(`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`) and under
`bin/simple test` — the viable-probe resolver landed green there
(parity 17/17, resolver spec 6/6).

## Root cause (2026-08-02, probe-bisected)

Two independent crashes hid under the one symptom, and the engine attribution
in the original report was inverted for the `lower` message:

1. **`lower` on nil = INTERPRETER crash, not JIT.**
   `src/lib/nogc_async_mut/env/platform.spl` `detect_os()` (the copy that
   `std.gc_async_mut.env.platform` re-exports and `backend_metal.spl` imports
   for `is_macos()`) did `val os_env = env_get("OS"); if os_env != "": if
   os_env.lower()...`. `env_get` returns nil for an unset var and `nil != ""`
   evaluates true, so on any host without `OS` exported the FIRST probe of
   every `"auto"` resolution (metal → `probe_metal` → `is_macos` →
   `detect_os`) called `.lower()` on nil:
   `error: semantic: method `lower` not found on type `nil``. The very next
   line, `env_get("OSTYPE").lower()`, was equally unguarded. Probe evidence:
   with the browser_engine renderer in the unit, interpreter mode died at
   exactly `Engine2D.probe_backend(1,1,"metal")` before any
   `[backend-resolve]` line; a direct `detect_os()` call reproduced it, while
   the JIT engine ran the same probe fine. (Without the renderer in the unit
   the interpreter took a code path that never hit the guard — which is why
   the resolver spec stayed 6/6 green.)

2. **The JIT crash at the same call site was a different defect:** the deep
   probe's mismatch branch (`probe_backend_viable`, engine.spl) called
   `engine.shutdown()` on the `"directx" → "directx-software-emulation"`
   fallback engine. That name matches no typed arm in `shutdown()`, so it
   falls to the duck-typed `self.backend.shutdown()` (engine.spl:2718 pre-fix
   numbering); in a JIT unit that also contains browser_engine the impl's
   vtable is absent and the call traps: `runtime error: duck-typed virtual
   method call (trait has no `impl Trait for ...` in unit; no vtable)`,
   SIGILL — the known jit_game2d_backend_method_dispatch_sigsegv_2026-07-02
   family.

## Fix (.spl-side, landed in WC 2026-08-02)

- `src/lib/nogc_async_mut/env/platform.spl`: nil-check before `.lower()` in
  `detect_os()` (OS, OSTYPE) and `detect_arch()` (PROCESSOR_ARCHITECTURE,
  HOSTTYPE, MACHTYPE) using the `if x == nil: "" else: x.lower()` pattern.
- `src/lib/nogc_sync_mut/env/platform.spl`: same guard for its `detect_os()`
  (sibling copy of the same family).
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl` `probe_backend_viable`:
  only call `engine.shutdown()` on the mismatch branch when the created name
  has a typed shutdown route (`engine2d_shutdown_has_typed_route`); a skipped
  fallback probe engine is an 8x8 CPU-raster surface with no device
  resources, probed once per process (memoized).

Verified: `simple_web_engine2d_resolved_backend_name(48, 32, "auto")` probe
now completes under bare `bin/simple run` (JIT: `selected cpu_simd`, exit 0)
and `SIMPLE_EXECUTION_MODE=interpreter` (`selected cuda`, exit 0). Residual
engine divergence (JIT rejects CUDA as unavailable, interpreter selects it)
is pre-existing backend-availability divergence, not this defect. The
remaining duck-typed probe calls in `probe_backend_viable` (b.clear/draw/
present/read_pixels on a matching GPU backend) still depend on the JIT
including the impl's vtable in the unit; the underlying JIT unit-construction
gap stays open under the 2026-07-02 bug.

## Status

Fixed at the .spl call sites (nil-guard + typed-route shutdown guard);
underlying JIT missing-vtable duck-dispatch defect remains open (tracked by
jit_game2d_backend_method_dispatch_sigsegv_2026-07-02).

## Verification 2026-08-17 (content classification) — duplicate-module hazard confirmed

Both named copies still exist and have **diverged**, which is the shadowing
precondition the doc suspected:

- `src/lib/nogc_sync_mut/env/platform.spl` — 356 lines
- `src/lib/nogc_sync_mut/platform.spl` — 192 lines
- `diff` reports the two files differ.

(Ten `platform.spl` files exist under `src/lib/` in total, across
`gc_sync_mut`, `gc_async_mut`, `nogc_async_mut`, `hardware`, `editor` and
`baremetal`; the two above are the pair reachable from the same
`nogc_sync_mut` prefix and so the pair that can shadow.)

Two same-named modules under one prefix, with different contents, is enough to
explain a backend auto-resolution landing on a module that lacks the method and
yielding "method lower not found on nil". Not enough, on its own, to prove it —
resolution order was not instrumented.

Not proven: no `Results:` line, and no JIT reproduction. This is a static
confirmation of the precondition only, not of the failure path.
