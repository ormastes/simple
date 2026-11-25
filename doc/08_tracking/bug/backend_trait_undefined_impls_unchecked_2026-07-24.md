# Compiler `Backend` trait is declared nowhere; impls silently unchecked
## Closed 2026-11-25 — defect no longer present at HEAD (verified by source inspection)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Resolution verification 2026-11-25 (work/p2w1-aj-20261125, release/1.0.0 HEAD)

STALE — the defect described here no longer exists in the pure-Simple tree;
closing by source inspection on `origin/release/1.0.0` (21e831c0a9b):

- **No live `impl Backend for <Type>` remains.** Repo-wide grep of
  `src/compiler` finds exactly one occurrence, commented out at
  `src/compiler/70.backend/backend/interpreter.spl:150`
  (`# impl Backend for InterpreterBackendImpl:` with the note "Trait
  implementation syntax not supported by runtime parser"). The five impl
  blocks named in this doc (compiler.spl, sdn.spl, interpreter.spl,
  jit_interpreter.spl, gpu_backend_shared_interface_parity.spl) were removed
  in later refactors; the parity file now only checks the *Rust seed* source
  for the string (`gpu_backend_shared_interface_parity.spl:111`).
- **`Backend` now resolves to a real type.**
  `src/compiler/70.backend/backend/backend_api.spl:166` declares
  `type Backend = CompilerBackend` (a class with `for_target`/`create`
  factories), so the `export Backend` at `backend/__init__.spl:15` is honest.
  The doc's "no `trait Backend` anywhere" complaint is moot: nothing impls an
  undefined trait because nothing impls `Backend` at all.
- The dangling-vtable stage4 link failure cannot recur via this path: with no
  `impl Backend for` blocks, there are no vtable_impls to skip or emit.

The doc's suggested fix (declare `pub trait Backend:`) was NOT taken; the
tree instead removed the impls and made `Backend` a type alias. The residual
idea — a lint for `impl T for X` where `T` resolves to no trait — remains a
separate, unfiled tooling suggestion, not part of this defect.

Verification limit: the pinned seed binary at HEAD rejects
`@representation_boundary` repo-wide, so no `bin/simple.exe check`/`test`
could run; this closure is by code inspection only.
