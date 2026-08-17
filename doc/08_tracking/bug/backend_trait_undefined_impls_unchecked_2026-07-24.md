# Compiler `Backend` trait is declared nowhere; impls silently unchecked

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Date:** 2026-07-24
**Area:** compiler / 70.backend
**Severity:** medium (masked type-safety hole; broke stage4 native link until seed workaround)

## Symptom

Stage4 full-CLI native link on macOS failed with undefined symbols:

```
___vtable__backend__backend__compiler__CompilerBackendImpl__for__Backend
___vtable__backend__backend__sdn__SdnBackendImpl__for__Backend
```

## Root cause

`src/compiler/70.backend/backend/compiler.spl`, `sdn.spl`, `interpreter.spl`,
`jit_interpreter.spl`, and `gpu_backend_shared_interface_parity.spl` all declare
`impl Backend for <Type>` — but **no `trait Backend` is defined anywhere in
`src/compiler`**. `backend/__init__.spl:15` claims `export Backend` "re-exported
from backend_api.spl", yet backend_api.spl has no such trait (it was likely lost
in a refactor). The only `trait Backend:` in the tree is the unrelated DI
library trait in `src/lib/nogc_sync_mut/src/di.spl:255` (different methods:
`process`/`is_instruction_allowed`/`name`/`kind`).

Consequences:

- The interpreter tolerates impls of undefined traits, so nothing ever
  type-checked those five impl blocks against a trait contract.
- In the seed native pipeline, MIR lowering skips `vtable_impls` when
  `trait_infos` lacks the trait (silent), while the project-wide scan in
  `imports.rs` marked the impl targets vtable-bearing — emitting dangling
  vtable references at every StructInit. Fixed on the seed side 2026-07-24
  (imports.rs now gates on the trait being defined), which unblocks the link
  but leaves the missing declaration itself.

## Proper fix (pure-Simple)

Declare `pub trait Backend:` (name, kind, process_module, process_function,
process_class, process_struct, process_enum, process_trait, process_impl,
eval_expr, exec_stmt, is_allowed, is_allowed_stmt) in
`backend_types.spl`/`backend_api.spl`, verify all five impls conform, and keep
`export Backend` honest. Then the vtable path becomes fully consistent again
(seed gate simply stops firing).

Also worth a lint: `impl T for X` where `T` resolves to no trait definition
should at least warn.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STILL-OPEN

`grep -rn "trait Backend" src/compiler --include=*.spl` returns ZERO declarations,
while the type is still used as a field/param type and the only impl is commented out:

```
src/compiler/70.backend/backend/interpreter.spl:97:# impl Backend for InterpreterBackendImpl:
src/compiler/70.backend/backend/env.spl:22:    backend: Backend
src/compiler/70.backend/backend/env.spl:203:    backend: Backend
src/compiler/70.backend/backend/env.spl:207:    static fn new(backend: Backend, module: HirModule) -> HirVisitor:
```

Owner path: src/compiler/70.backend/**.
