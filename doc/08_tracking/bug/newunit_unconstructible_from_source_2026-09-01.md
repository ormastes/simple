# `newunit` declares a type that cannot be constructed from source; its spec never tries

**Date:** 2026-09-01
**Found by:** parent session, while retesting a workstream-I claim.
**Status:** OPEN. Disqualifies `newunit` as the vehicle for goal G7
(typed addresses) in `doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md`.

## Measured (seed binary — see caveat)

Syntax recovered from `test/01_unit/compiler/types/units_newunit_registry_spec.spl:9`
(`newunit Name: T as suffix`).

| form | result |
|---|---|
| `newunit LbaU: i64 as lba` | **parses cleanly** |
| `takes_lba(7lba)` — suffix literal | parse error: `function arguments: expected Comma, found Identifier { name: "lba", pattern: Immutable }` |
| `takes_lba(LbaU(7))` — constructor call | `error[E1002]: function 'LbaU' not found` |

The declaration is accepted; no value of the declared type can then be built by
any form tried. The feature is unusable from source.

## Why no test caught it

`test/03_system/app/compiler/feature/world_units_newunit_spec.spl` exercises only
the **registry API**: it calls `newunit_register("WunUserId", "wuid", TYPE_I64)`
directly and asserts on `short_symbol`, `full_symbol`, `kind`, `klass`, and
`base_factor` (1/1). It **never declares a `newunit` in surface syntax and never
constructs a value of one.**

So the spec is green against the compiler-side registry while the user-facing
feature does not work. This is the "a scan that finds nothing may have scanned
nothing" failure mode applied to a feature spec: the test proves the bookkeeping,
not the feature.

## Required

1. A spec that declares a `newunit` in surface syntax, constructs a value, passes
   it to a function, and reads it back — i.e. the path a user would take.
2. Either a working construction syntax, or an explicit statement that `newunit`
   is a compiler-internal registry with no surface form (in which case the
   language docs and `primitive_classification.spl`'s recommendation of wrapper
   types for `PhysAddr`/`VirtAddr` at `src/compiler/35.semantics/lint/primitive_classification.spl:110,113`
   should not imply otherwise).

## Related, and explicitly NOT confirmed here

Workstream I reported that `newunit` silently scales values ×8 (`<<3`), violating
REQ-WUN-001's identity base factor. **The parent could not construct a `newunit`
value by any accepted form, so that claim is neither confirmed nor refuted** and
must not be cited as established.

## Caveat

Measured on the **Rust bootstrap seed** (`bin/simple` prints the non-production
warning). Self-hosted retest is blocked by the bootstrap redeploy failure. Do not
close on a seed-only fix. See
`doc/08_tracking/bug/function_argument_types_unchecked_2026-09-01.md`, which
carries the same caveat.
