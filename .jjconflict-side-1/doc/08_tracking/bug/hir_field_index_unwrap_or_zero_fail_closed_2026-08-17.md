# Field-index resolution ended in `.unwrap_or(0)` — now fails closed

**Status:** FIXED (Rust seed lowering) / stage-3 symptom NOT attributable to this file
**File:** `src/compiler_rust/compiler/src/hir/lower/expr/access.rs` (was line 291)
**Date:** 2026-08-17

## Defect

In the `CannotInferFieldType` fallback of `lower_field_access`, field-index
resolution ended in `.unwrap_or(0)`. `0` is a valid index for every non-empty
struct, so an unresolved index produced a silently wrong read — right shape,
right type, wrong value — instead of a diagnostic.

## Fix

Three attempts, then fail closed:

1. `get_field_info(recv_hir.ty, field)`
2. `try_resolve_global_field_index_by_name(candidate, field)`
3. **new** `try_resolve_registry_field_index_by_name(candidate, field)` — the HIR
   type registry, whose declaration order IS the field index; it is the same
   table the field TYPE was just resolved from, so a struct whose type resolved
   by name can always resolve its index by name.

`None` now returns `LowerError::CannotInferFieldType { struct_name, field,
available_fields }` — the struct and field are named, and `available_fields`
comes from the registry. `SIMPLE_FIELD_INDEX_COUNT_ONLY=1` keeps the old
guess and prints `[field-index-unresolved] struct=… field=…` instead; it exists
only for measuring latent breakage.

## Measured latent breakage: ZERO — shipped big-bang, no staging

Corpus: the whole bootstrap closure, built with the Rust `native_project`
pipeline from a clean `origin/main` worktree plus this patch only
(`CARGO_TARGET_DIR=/mnt/data/cargo-target-fieldidx`):

```
SIMPLE_FIELD_INDEX_COUNT_ONLY=1 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 \
  simple native-build --source src/compiler --source src/lib --source src/app/cli \
  --entry src/app/cli/bootstrap_main.spl -o /tmp/fi_stage2
Build complete: 862 compiled, 0 cached, 0 failed
unresolved: 0   recovered-by-attempt-3: 0
```

862 modules, **0** unresolved and **0** third-attempt recoveries: on this corpus
the first two attempts always succeed, so failing closed cannot regress it. A
second instrumented build (recovery counter added) reproduced both zeros.

## The stage-3 symptom is NOT this file

`-hir-field-type struct=CompiledUnit field=entry_point actual=2589120870-` is
printed by `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:732`
— **pure-Simple** lowering, a field-TYPE discriminant check, not this Rust
field-index fallback. Stage 3 is the stage-2 *pure-Simple* compiler recompiling
itself, so `access.rs` is not on that path at all. That directory is claimed by
another lane; not touched here.

## Evidence, both engines (fixture: struct returned by value, read via a local,
directly off the call, and through a forwarding return; values 11/13/17)

| path | result |
|---|---|
| deployed `bin/simple` (default pure-Simple driver, `--entry-closure`) | `DIRECT 1 1 1  CALL 1 1 1  FWD 1 1 1` — **every field reads `1`** |
| patched seed, `SIMPLE_NATIVE_BUILD_RUST=1` | `DIRECT 11 13 17  CALL 11 13 17  FWD 11 13 17` |

Class fixture (2-, 5-, mixed-type-, nested-field structs, all read off call
results):

| path | result |
|---|---|
| deployed `bin/simple` | binary built, then **SIGSEGV at 0x48** at runtime |
| patched seed, Rust pipeline | `TWO 41 43  FIVE 51 59 67  MIXED 71 LBL  OUTER 73 79 83` |

So the `reads-as-1` / SIGSEGV behaviour lives on the **pure-Simple** native
path, not in the Rust lowering fixed here. Filed as an observation, not fixed.

## Specs

- reproducing: `test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl`
- class detection: `test/01_unit/compiler/hir/field_index_guess_class_spec.spl`

Both shell out (a spec body runs interpreted and can never see this). Against
the **deployed** `bin/simple` they are legitimately RED for the pure-Simple
defect above, per `.claude/rules/testing.md` ("a correct spec that fails is a
legitimate artifact"). A full `bin/simple test` run of the class spec was
killed at 600s before its body ran (`rc=143`, no `Results:` line) — that run is
UNVERIFIED, not failed; the table above is direct fixture evidence instead.
