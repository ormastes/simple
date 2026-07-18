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
