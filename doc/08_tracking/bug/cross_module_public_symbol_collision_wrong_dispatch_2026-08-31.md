# Cross-module PUBLIC symbol collision silently dispatched to the wrong function (2026-08-31)

Status: **FIXED** for the MIR direct-call path (this change). Two adjacent shapes
remain open and are named below — neither is closed by this fix.

## Symptom

A caller that *selectively* imports `m1.pick(i64)` and calls it with an `i64`
executes `m2.pick(bool)`'s body instead. Wrong value, exit code 0, no error.
Whether it misdispatches depends only on module load **order**, so the same
source is right or wrong depending on the order of unrelated `use` lines.

Reproducer, now a spec:
`test/01_unit/compiler/driver/public_dup_signature_dispatch_spec.spl`
(RED on the pre-fix seed: `got=222`; GREEN after: `got=111`).

## Root cause

`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs`, the
`private_dup_overloads` block, gated its collision scan on
`name.starts_with('_')`. Only `_`-prefixed private helpers ever got `$dupN`
variants; every colliding **public** free function got none at all, so its call
sites fell straight through to plain last-write-wins in codegen — no type check,
no arity check, only a warning.

The warning text (`compiler_cross_module_private_symbol_collision`) understated
this: it says call sites "resolve by exact arg-type match (mangled `$dupN`
variants)". For 265 of the 359 colliding names, no `$dupN` variant existed and
no arg-type match was ever attempted.

## Fix

Consider public free functions in the collision scan too, mangling all but the
**last** definition. The last definition keeps the bare name deliberately: only
the direct-call branch of `lowering_expr_call.rs` consults
`private_dup_overloads`, so indirect calls (function taken as a value), extern
imports and every by-name symbol lookup still resolve the bare name. Keeping the
last one bare makes all of those resolve exactly as they do today
(last-write-wins) while exact-signature direct calls now reach the right body.
`_`-prefixed helpers keep their existing all-mangled scheme unchanged.

Evidence: `cargo test -q -p simple-driver --lib` 494/494; 27 real unit specs
(lib/common, compiler/pipeline, app/mcp, os/services/vfs) byte-identical
example/failure counts on the pre-fix and post-fix seeds, 0 differences; the new
spec RED->GREEN; the indirect-call case covered by its second example.

## Census (from a full suite run, ~12,000 units, 13,439 raw warning occurrences)

Raw occurrence counts are heavily duplicated per unit. Distinct populations:

| population | count |
|---|---|
| distinct colliding free-function names | **359** |
| — public functions (were **unprotected**) | **265** |
| — `_`-prefixed private helpers (were protected) | 94 |
| distinct (name, signature-set) groups | 376 |
| distinct colliding **class** names (separate shape) | 44 |

Location of the 359 (358 located by definition scan, 1 unlocated):

| where defined | count |
|---|---|
| `src/` only | 278 |
| mixed `src/` + `test/` | 80 |
| `test/` only | 1 |

So this is overwhelmingly product code, **not** test fixtures, and **not**
deliberate parallel stdlib twins: only 4 of the 359 are the same relative path
under two different `src/lib/<layer>/` trees. The rest are genuine accidental
collisions of common names (`env_get`, `join_path`, `shell`, `process_wait`,
`errno_of`, `read_file`, `make_tool_error`, …) across unrelated modules.

Per-name data: `doc/08_tracking/bug/data/cross_module_symbol_collision_census_2026-08-31.tsv`

## Options considered

- **(a) rename the colliding helpers.** 358 names across product code, most of
  them public API. Rejected as the primary fix: it is a very large breaking
  data change and it does not remove the hazard for any collision added later.
- **(b) make mangling collision-proof.** Adopted, in the narrow form above.
  The full form (module identity in every mangled name) was *not* adopted —
  it changes every symbol name and its blast radius reaches native linking,
  SMF manifests and the interpreter's by-name lookups.
- **(c) promote the warning to an error.** Would fail 359 distinct names and a
  large fraction of the ~12,000-unit suite immediately. Not viable today; it
  becomes viable only after the population is paid down.
- **(d) ratchet the population** the way
  `scripts/check/check-unbacked-extern-ratchet.shs` ratchets unbacked externs.
  **Still recommended and NOT implemented here.** With (b) landed the direct-call
  hazard is gone, but the two open shapes below are not, and the population can
  still grow. A ratchet freezing the 359 names and failing on any new one is the
  right next step.

## Still open (not closed by this change)

1. **Same-signature collisions.** Two definitions with an *identical* signature
   still last-write-wins by design (`lowering_core.rs` leaves the name alone),
   and the diagnostic for it is default-OFF (`same_signature_diag_enabled`).
   The emitter's own comment in
   `src/compiler_rust/compiler/src/pipeline/module_loader.rs` describes this as a
   silent wrong answer and the mechanism behind a vacuity class. Existing RED
   guard: `test/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.spl`.
   The true size of this population is unmeasured, because the diagnostic is off.
2. **The cranelift JIT half.** `test/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.spl`
   passes on the interpreter and fails on the cranelift JIT — verified failing
   **identically on the pre-fix and post-fix seeds**, so it is a separate
   resolution path this MIR-lowering fix does not reach, not a regression.
3. **Class-name collisions**: 44 distinct names, resolved by bare name in the
   interpreter's class registry, so any cross-module duplicate mis-dispatches.
   Untouched here.
