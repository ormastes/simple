# signal_handlers.spl `_global_cleanup_handler` cross-module fn-pointer misresolved as DATA export

Status: Open.

Date: 2026-07-17

## Status

Open. Found by the scanout lane while chasing the SimpleOS x86_64 desktop
screendump goal; outside that lane's task closure under the correct build
recipe (`--entry-closure --backend cranelift --target x86_64-unknown-none`).
Needs its own repro + fix.

## Context

`_global_cleanup_handler` is a module-level function-pointer variable:

```
var _global_cleanup_handler: fn() = default_cleanup_handler
```

declared in both `src/app/io/signal_handlers.spl:35` and
`src/lib/nogc_sync_mut/io/signal_handlers.spl:35`. It is reassigned by
`register_cleanup_handler`-style setters (`_global_cleanup_handler =
cleanup_handler`, e.g. line 66 in both files) and invoked as a plain call
(`_global_cleanup_handler()`) from several signal-handling entry points (lines
92/107/122/133 in `src/app/io/signal_handlers.spl`; 93/108/123/136 in
`src/lib/nogc_sync_mut/io/signal_handlers.spl`).

Under native-build, a cross-module call through this fn-pointer variable is
misresolved as a DATA export (i.e. treated as a plain data symbol reference
rather than an indirect call through the stored function pointer), rather than
loading the current pointer value and calling through it. This is the same
general class of module-global / cross-module symbol resolution defect already
catalogued for other freestanding/entry-closure build issues (see
`doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`,
C1: module-global `val/var X = call()` initializers never emitted), but this
specific case is about a **function-pointer-typed** global being called across
module boundaries, not a call-initializer being skipped.

## Impact

Any consumer of `signal_handlers.spl` that reassigns `_global_cleanup_handler`
from one module and expects the call sites in another module (or even the same
module under some builds) to observe the updated pointer is at risk of instead
invoking the DATA export's address directly (i.e. not going through the
indirection), or of the call being linked against a stale/incorrect target.
This was not the render-stability lane's own blocker (the desktop kernel build
under the canonical WM recipe doesn't reach this code path in its own closure)
but the scanout lane's investigation surfaced it as a real, reproducible
cross-module resolution defect worth tracking.

## Required fix

1. Build a minimal repro: two Simple modules, one declaring/reassigning a
   `fn()`-typed module-global, the other calling it, under
   `native-build --entry-closure --backend cranelift --target
   x86_64-unknown-none`. Confirm via `nm`/`objdump` whether the call site
   resolves to a `call [got-relative load]`-style indirect call through the
   variable's storage, or a direct `call <symbol>` against what the linker
   treated as a data export.
2. Root-cause in the compiler's symbol/export classification for fn-pointer
   typed globals under freestanding entry-closure codegen (likely
   `codegen/common_backend.rs` or the MIR global-lowering path, given the
   family resemblance to the C1-C8 defects already tracked).
3. Fix at the compiler level (out of scope for OS/UI lanes) so
   `_global_cleanup_handler`-style call sites always dereference the current
   stored pointer rather than being treated as a direct/data reference.

## Additional reproduction — pure-Simple test runner entry

The Cycle 11 pure-Simple bootstrap candidate reproduced this defect while
building the smaller `src/app/test_runner_new/main.spl` entry closure with
unsafe stub fallback disabled. Compilation rejected `on_sigint`, `on_sigterm`,
`on_sighup`, and `on_normal_exit` because `_global_cleanup_handler` resolved to
the DATA export
`nogc_sync_mut__io__signal_handlers___global_cleanup_handler` where codegen
required a function. This confirms the defect also blocks an admitted native
test runner, independently of the monolithic CLI graph-load timeout.

## Bootstrap rewrite diagnosis — 2026-07-17

The fresh Stage 2 runner disproved the initial stale-artifact hypothesis: it
reproduced the same data-export error. The native-project bootstrap rewrite was
erasing the decisive type before HIR by changing the top-level callback slot
from `fn()` to `any`. Consequently `global_init_functions` omitted the slot and
MIR emitted a direct `Call` to a data export instead of loading the current
pointer and emitting `IndirectCall`.

The rewrite now preserves top-level `var`/`val`/`static`/`const` function slots
only when their initializer is an identifier or path. Struct fields, locals,
and lambda initializers retain the compatibility rewrite to `any`. A focused
bridge regression applies the bootstrap rewrite, parses and lowers its output,
then checks the HIR initializer map and MIR `GlobalLoad` + `IndirectCall` shape.

The canonical bootstrap-only driver, native runtime, and compiler-backfill
artifacts were rebuilt separately from current source. Using that fresh seed
once with a new cache produced `build/native_probe/simple-stage2-fresh`: 715
units compiled, zero failed, linked in 397.6 seconds. That fresh Stage 2 still
reproduced the bug and established the rewrite as one active cause.

A second rebuild with the corrected backfill also produced a 715-unit Stage 2,
but that pure-Simple compiler reproduced the direct-call error while building
the runner. Its MIR lowering registered module globals only when their
initializer folded to a scalar constant; a function identifier does not.
Calls also reclassified only locals, never mutable module storage. The
pure-Simple fix registers every module binding before folding, resets the
module-local SymbolId set between modules, and reclassifies calls through a
real `MirStatic` as indirect. Its regression covers handler reassignment via
`StoreGlobal` and invocation via `LoadGlobal` + `CallIndirect`.

The default function initializer still lacks a general pure-Simple static
relocation representation; the signal-handler path assigns the requested
cleanup function before installing callbacks, so that separate semantic gap
does not block this runner.

Final bounded-cycle evidence rebuilt `libsimple_native_all.a`, then produced a
715-unit Stage 2 with zero failures. That compiler compiled and code-generated
the standalone runner without any `_global_cleanup_handler` data-export
diagnostic, confirming this defect is fixed on the exercised path. Subsequent
non-bootstrap builds selected a freshly generated `core-c-bootstrap` archive
without a runtime-path override; they also reached linking with no callback
data-export failure, then stopped on the runner's separate core-C ABI gap.
That blocker is tracked in
`pure_simple_test_runner_core_c_runtime_abi_gap_2026-07-17.md`. Runner
execution and broad Cranelift function-static support remain open; the
function-pointer compiler fix itself is retained with focused regressions.
