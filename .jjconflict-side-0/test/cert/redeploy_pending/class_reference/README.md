# Staged specs — class reference / object-handle model (Patch 3)

These `.spl` programs are **STAGED / FROZEN**. They exercise the interpret-mode
class-reference fix that is compiled into a NOT-yet-redeployed binary, so they
would fail on the currently-deployed `bin/simple`. Do **not** move them into the
active test suite (`test/**`) until the compiler is rebuilt and redeployed.

See `doc/03_plan/cert/redeploy_kit/ACTIVATION_MANIFEST.md` § "Patch 3 — class
reference model" for the commit sha, files touched, and post-redeploy activation.

## The bug (tasks #99(d) / #112)

Interpret mode (`SIMPLE_EXECUTION_MODE=interpret`, i.e. `CompileMode.Interpret`
-> `InterpreterBackendImpl`, the 70.backend engine) dropped mutations to a class
instance read out of an array: the repro printed `42` (stale) while default /
JIT printed `777`. See
`doc/08_tracking/bug/jit_class_mutation_drop_characterization_2026-07-04.md`.

## Root cause and fix

The class reference / `ObjectStore` handle model (class instances = a shared
`Value.Object(handle)` record) was already landed in commit `19cd165d238`
(`objects.spl`, `Value.Object` handle, `env.store`, field read/assign through the
store). The remaining gap: the 70.backend interpreter had **no `HirExprKind.Index`
read arm**, so `arr[0]` fell through to `not_implemented` and the class-in-array
repro could not run on this engine at all. Patch 3 adds the `Index` read arm; it
returns the array element verbatim, and because a class element is a
`Value.Object(handle)`, every holder shares the one store record — reference
semantics fall out for free.

## Files and expected output

| File | Mode to verify | Expected stdout | What it proves |
|---|---|---|---|
| `class_in_array_mutation.spl` | `SIMPLE_EXECUTION_MODE=interpret` (and default) | `777` | class read out of an array + mutated through the alias is visible via the array slot (the core repro; was `42`) |
| `shared_alias_mutation.spl` | `SIMPLE_EXECUTION_MODE=interpret` (and default) | `777` | two vars bound to one instance share state (aliasing not regressed) |
| `struct_value_copy.spl` | default `bin/simple run` | `42` | STRUCTS still value-copy — mutating a copy does not affect the original |

`struct_value_copy.spl` is verified under DEFAULT mode: struct field assignment
is a separate, still-unimplemented path in the interpret-mode 70.backend engine
(field-assign there routes only class Objects through the store). That gap is NOT
part of this patch; an interpret-mode error on that file is not a regression of
the class-reference change.
