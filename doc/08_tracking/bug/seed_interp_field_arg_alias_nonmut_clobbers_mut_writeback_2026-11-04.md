# Seed interpreter: non-`mut` `obj.field` alias reverts `mut` param write-back

Date: 2026-11-04. Status: FIXED (seed interpreter).

Shape `nested_field_aliased` of `test/01_unit/language/probe_engine_divergence_mutation_class.spl`:
`nested_field_arg(h3.items, h3.items)` with `fn nested_field_arg(mut items: [i64], other: [i64])`.
Interpreter printed 1, JIT printed 2 (correct: `mut` params alias, caller observes the push).

Root cause: `write_back_mutable_arguments`
(`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`, `ArgSource::Field` arm)
wrote back the non-`mut` parameter's stale pre-call snapshot after the `mut` one, reverting it.
The identifier arm already guarded this with `mut_written`; the field arm did not.

Fix: track `(obj, field)` pairs written by a `mut` param and skip non-`mut` write-backs to them.
Not related to the pure-Simple T1 bug `pure_simple_interp_copies_mut_struct_param_2026-11-04.md`.

Cross-arm follow-up: the Ident and Field arms now consult each other's mut-written sets
(`f(h.items, h)` and `f(h, h.items)`, struct and class); four shapes added to the probe/spec.

Known remaining gap: nested receiver `o.h.items` is not written back (the Field arm requires an
Identifier receiver, ~function_exec.rs:1670); interpreter 1 vs JIT 2.

Known remaining gap (class): `f(x.items, x)` with `fn(mut items: [i64], b: Box)` where `Box` is a
`class`: interpreter 1, JIT 2. In the Field arm the caller's `x` reads as `Nil` at write-back time
(obj_val == Nil; the aliased class arg appears moved out of the frame), so nothing can be written.
Struct variant fixed. Not in the probe; needs a call-binding/move investigation.
