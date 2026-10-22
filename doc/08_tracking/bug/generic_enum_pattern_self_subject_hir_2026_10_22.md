# Self-hosted HIR rejects generic enum patterns on self/field subjects (2026-10-22)

Status: WORKED AROUND in `poll.spl` / `future.spl` (bind the subject to a
typed local, or delegate to a module-scope free function taking the value as a
parameter). The underlying self-hosted HIR limitation remains open.

## Symptom

The stage2 candidate's HIR lowering failed exactly two modules of the 1438-module
`bootstrap_main.spl` entry closure:

```
src/lib/nogc_async_mut/async/poll.spl:
  generic enum pattern requires concrete declaration-ordered type arguments
  unresolved name: value at poll.spl:28
src/lib/nogc_async_mut/async/future.spl: (same class)
```

## Root cause

`hir_lowering/_Expressions/expression_components.spl` (~line 441-446): for a
generic enum pattern, the SUBJECT's type arguments must be concrete
(`declared_pattern_slot_types_are_concrete(subject_arguments)`). Inside
`impl Poll<T>`, matching directly on `self` (or on `self.poll_result`) resolves
the subject's type arguments non-concretely and the lowering errors out. The
seed's Rust HIR accepted the same source, so stage2 (seed-produced) compiled
these files and only the self-hosted recompile (stage 3) exposed the gap.

The accepted shape: a generic enum value matched through a function PARAMETER
or a locally-bound `val` of the declared generic type lowers cleanly — the
`task_poll_result_*` free functions in
`src/lib/common/contracts/execution/simple_ring_async_v1.spl` already use it
and pass.

## Fix applied

- `poll.spl`: impl methods delegate to `poll_is_ready<T>` / `poll_unwrap<T>`
  module-scope free functions taking the `Poll<T>` value as a parameter.
- `future.spl`: each `match self.poll_result` now binds
  `val current: Poll<T> = self.poll_result` first and matches `current`.

Both files verified compiling under the stage2 candidate compiler.

## Proper repair (not done)

Teach the self-hosted HIR to resolve `self`/field subjects inside a generic
impl to the impl's type-parameter bindings (declaration-ordered) and accept
them the way parameter subjects are accepted, with the payload substitution
the existing code path already performs.
