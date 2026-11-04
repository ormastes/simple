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

Both remaining gaps FIXED (2026-11-04), shapes added to the probe/spec (14 shapes):
- Class `f(x.items, x)`: root cause was `park_written_back_arguments` parking `x` (identifier arg,
  replaced by a `Nil` placeholder) so the Field arm read `x` as Nil. Fix: never park a name that is
  also the root of a field-access argument receiver.
- Nested receiver `f(o.h.items, ..)`: the Field arm now walks the receiver chain
  (`field_receiver_path`) and writes back copy-on-write through the path (`set_nested_field`);
  nested paths write back only for an explicit `mut` parameter.
