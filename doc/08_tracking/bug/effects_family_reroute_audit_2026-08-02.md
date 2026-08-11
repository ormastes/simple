# effects_* family: 4 of 8 modules deleted, 4 retained with the reroute proved

**Date:** 2026-08-02
**Status:** Partially resolved — 4 modules deleted, 4 filed here with a measured
reason to leave them.
**Follows:** `effect_pass_dead_and_stub002_falsely_fixed_2026-08-01.md`, which
deleted the only consumer of this family and deliberately did NOT delete the
family itself.

## Why this needed measuring rather than a bulk delete

`src/compiler/00.common/__init__.spl` re-exported the SAME names from FOUR
modules — `EffectTag`, `EffectEnv`, `EffectStats` and `FunctionEffectInfo` each
appeared in more than one `export use` line. Deleting a module that participates
in such a set does not deduplicate the name; it REROUTES it to whichever
definition survives.

Worse, resolution is not confined to declared import paths. Importing one symbol
from a module registers **all** of that module's top-level functions into a flat
global registry, so a body can win a name with no declaration path pointing at
it. That is not theoretical here — see the `effects_phase3a.spl` finding below.

Everything below was proved by RUNNING, with the winning body identified by
instrumentation or by a field/method only one candidate has.

## Deleted — 4 modules, 109 lines

| Module | Lines | Why it was safe |
|---|---|---|
| `effects_env.spl` | 10 | **Defines nothing.** Whole file is a docstring plus `use compiler.common.effects.{EffectTag, EffectEnv, init_builtins}`. A module with no definitions cannot own a name, so no body can be rerouted by removing it. |
| `effects_v1_simple.spl` | 10 | Same shape: a pure re-export shim with zero definitions. |
| `effects_promises.spl` | 45 | 4 free functions, zero consumers outside the family. One name, `needs_promise_wrapping`, genuinely collides — see below. |
| `effects_scanner.spl` | 44 | Defines `struct ScanResult`, which collides with two other `ScanResult` definitions that DO have live consumers — see below. |

`EffectTag`, `EffectEnv`, `EffectStats` and `init_builtins` are unaffected: all
three shim paths resolved to the single definition in `effects.spl`, which is
still exported from `__init__.spl` line 62.

### `needs_promise_wrapping` — collision measured, no reroute

Two free functions share the name:

- `00.common/effects_promises.spl` — `(func_name: text, env: EffectEnv) -> bool`
- `30.types/type_system/effects.spl` — `(func: FunctionInfo, env: Dict<text, Effect>) -> bool`

(A third, in `30.types/type_check/mod.spl`, is a **method** invoked as
`self.needs_promise_wrapping(...)`. Method dispatch, not the free-function
registry. Not a participant — an early reading had it wrong.)

Measured by putting a distinct `print` in each body and calling the name with
both `compiler.common` and `compiler.types.type_system` imported:

- before deletion: `BODY: 30.types/type_system/effects`
- after deletion:  `BODY: 30.types/type_system/effects`

The 00.common body never won, so removing it cannot change the winner. Verified,
not assumed.

### `ScanResult` — three definitions, winner unchanged

- `00.common/effects_scanner.spl` — `struct` (deleted)
- `10.frontend/desugar/spawn_analysis.spl` — `struct { sites, found_await }`
- `90.tools/depgraph/scanner.spl` — `class`

Constructing `ScanResult(sites: [], found_await: true)` through the facade
returned the desugar struct both before and after the deletion, with zero
unresolved-import warnings.

## Retained — 4 modules, 829 lines, each with a measured reason

### `effects_phase3a.spl` (28 lines) — DELETING IT REROUTES A LIVE NAME

This is the stop-and-report case, and it is the sharpest illustration of the flat
registry. The file is re-exported by **nothing** and imported explicitly by
**nothing** — by declaration it looks unreachable. It is not.

It defines a third `enum Effect` (alongside `30.types/type_system/effects.spl`
and `50.mir/mir_effects.spl`) with `impl Effect: fn is_async()`. Calling
`Effect.Async.is_async()` with `compiler.common` and `compiler.types.type_system`
imported gives:

- with the file present: `error: method 'is_sync' not found` — i.e. `is_async`
  RESOLVED, to this file's `impl`, and failed inside it
- with the file deleted: `error: method 'is_async' not found` — the resolution
  target is gone

The error changes, so the deletion changes which body a live name resolves to.
Not landed. It also carries a top-level `fn main`, the only one in `00.common`.

**Second-order finding worth its own lane:** the transcript above means
`30.types/type_system/effects.spl::needs_promise_wrapping` **cannot execute**
when `compiler.common` is also imported — its body calls `.is_async()` on an
`Effect`, and the enum that wins the name lacks a working method pair. That is a
live defect independent of this cleanup, and it is why probe A could not be
scored. It was not fixed here because fixing it means choosing an owner for the
`Effect` name across three modules.

### `effects.spl` (451), `effects_cache.spl` (102)

Both define a **different** `struct FunctionEffectInfo` — `effects.spl` has
`is_async`/`contains_suspension`; `effects_cache.spl` has
`declared_effects`/`violations` and a `static fn empty(name)`. Both are still
re-exported from `__init__.spl`.

Measured via `FunctionEffectInfo.empty("probe")`, which only the cache version
provides: the facade resolves to **`effects_cache.spl`**. So deleting
`effects_cache.spl` would reroute the name to a struct with different fields.
Neither is deleted.

### `effects_solver.spl` (248)

Consumer-free since `effect_pass.spl` was deleted, but it is re-exported as
`export use compiler.common.effects_solver.{EffectScanner, EffectSolver}` while
defining no `struct` or `enum` at all — so that export line names two symbols the
module does not appear to define. That is a pre-existing inconsistency this lane
did not create and did not measure. Left alone rather than deleted on top of an
unexplained export.

## Verification limits — stated plainly

No bootstrap was run. `bin/simple check` and `bin/simple lint` BOTH refuse on the
seed ("pure-Simple tool unavailable; refusing Rust fallback"), so there is **no
compile-level verification** of this change, exactly as with the two commits
before it. What exists is runtime module-graph evidence:

- positive control: the `compiler.common` facade plus the three retained
  `effects*` modules load with zero unresolved-import warnings
- negative control: importing a deleted module now fails — exit 1, marker absent,
  one unresolved-import warning. The discriminator is proved live, which matters
  because an unresolved `use` is otherwise only a WARNING and the process still
  exits 0; scoring a delete-verification on exit status alone is fail-open.

## Remaining

829 of 938 lines. Closing them out needs an owner for the `Effect` name (three
definitions) and for `FunctionEffectInfo` (two), which is a design call, not a
cleanup.
