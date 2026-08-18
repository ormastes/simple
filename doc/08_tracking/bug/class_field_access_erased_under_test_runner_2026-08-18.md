# Class field access erased under `bin/simple test` (seed 2026-08-18 10:12)

> **Same defect as [`selfhosted_child_erases_class_values_cross_module_2026-08-18.md`](selfhosted_child_erases_class_values_cross_module_2026-08-18.md)**,
> filed independently the same day by another lane agent. Scope reconciled:
> that record observed it only on values crossing a module boundary (and on
> METHOD dispatch as well as fields); this record is the broader and correct
> one — a fully self-contained spec with a local class fails identically, so
> the boundary is not the trigger. Read both; four independent confirmations
> exist (Logger in the compiler frontend, the component descriptor, the facet
> registry, and the native capsule receipt).


**Status:** RESOLVED (was OPEN) — seed regression, worked around in std.common.structural.component
**Binary:** /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
(59645008 bytes, mtime 2026-08-18 10:12:23) — the shared seed replaced mid-session.

## Symptom

Under `bin/simple test`, EVERY field access on a `class` value fails with
`semantic: undefined field '<name>': cannot access field on value of type
'object'`. Not limited to cross-module imports: a fully self-contained spec
with a local class and a top-level helper fn fails identically. The same code
passes under `bin/simple run`.

Minimal reproduce (fails 1/1 under `test`, passes under `run`):

    use std.spec
    class LocalBox:
        ok: bool
    fn box_ok() -> bool:
        val b = LocalBox(ok: true)
        b.ok
    describe "probe":
        it "field access": expect(box_ok()).to_be(true)

## Positive control

The identical spec with `struct LocalBox` instead of `class` passes:
`Results: 1 total, 1 passed, 0 failed`. Struct field access is unaffected.

## Impact evidence

- test/01_unit/lib/structural/component_descriptor_spec.spl was landed GREEN
  12/12 at 6ecf6ea6aae (2026-08-18 04:12). On the 10:12 seed it fails 12/12
  with the erasure error, code unchanged (verified by reverting to the
  committed tree and re-running).
- After converting the component descriptor records to `struct` it recovers to
  10/12; the remaining 2 failures access fields of `DynSmfManifestEntry`, a
  `class` in src/os/smf/dynsmf_session.spl (not converted here — different
  ownership lane).

## Workaround applied

src/lib/common/structural/component/descriptor.spl: pure-data records
converted `class` -> `struct` (they carry no methods; struct is the honest
shape anyway). Any spec-blocking class in other modules needs either the same
treatment or the seed fix.

## RESOLVED 2026-08-18 (lane-aspect-dynload)

Root cause: reference-identity `class` values (`ClassDef::is_value_type ==
false`) are stored as `Value::ClassInstance`, while `Value::Object` holds
value-identity `struct`s. Two interpreter dispatchers had arms only for
`Value::Object`:

- `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:358` (field read)
- `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1242` (method call)

`ClassInstance` fell into the catch-all, and `Value::type_name()` renders it as
`"object"` (`value_impl.rs:638`) — which is exactly why the receiver printed
with its correct class and fields while the static identity looked erased.
Both now have `Value::ClassInstance` arms; the method arm binds `self` to the
instance itself, preserving reference semantics.

Acceptance:
- test/01_unit/compiler/interpreter/class_value_field_access_spec.spl —
  `Results: 4 total, 4 passed, 0 failed`
- test/01_unit/compiler/interpreter/class_value_field_access_control_spec.spl —
  `Results: 4 total, 4 passed, 0 failed`
- test/01_unit/lib/structural/component_descriptor_spec.spl —
  `Results: 12 total, 12 passed, 0 failed`
- `run`-mode positive control unchanged (class field, class method, struct
  field, cross-module class field all correct).
