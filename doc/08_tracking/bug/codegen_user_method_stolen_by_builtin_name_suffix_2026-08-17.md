# Codegen: a user method whose name matches a builtin string method is stolen outright (returns 0)

Status: OPEN (P1)
Date: 2026-08-17
Severity: high (silent wrong result — compiles clean, exits 0)
Found by: the class-detection probe written for
`interp_me_method_first_param_times8_conditional_2026-06-29.md`

## Symptom

A user-defined method on a plain struct whose NAME matches a builtin string
method is not called at all — the JIT substitutes the runtime helper.

```spl
struct Collider:
    tag: i64

impl Collider:
    me char_code_at(v: i64) -> i64:
        v

fn main():
    print(Collider(tag: 0).char_code_at(42).to_text())
```

Observed (`SIMPLE_EXECUTION_MODE=jit bin/simple run`): `0`. Expected: `42`.
`SIMPLE_EXECUTION_MODE=interpreter`: `42` (correct). Exit code 0 in both cases.

Measured on `bin/release/x86_64-unknown-linux-gnu/simple` (59,536,728 bytes,
mtime 2026-08-16 22:59) AND on a seed rebuilt from current source
(`/mnt/data/cargo-target-c1b-a/release/simple`, 2026-08-17) — so it is live in
tree, not an artefact of a stale binary.

## Relationship to the append/push defect

Same FAMILY, different mechanism, and the distinction matters:

- `push`/`append` (FIXED 2026-08-17, `mir/lower/lowering_expr_method.rs:1606`):
  the user method WAS called, but MIR rewrote its first integer argument
  (tag-boxed it, `v << 3`), so the callee read `value * 8`.
- `char_code_at` (THIS bug): the user method is not called at all. The receiver
  is typed (`Collider`), so the qualified name `Collider.char_code_at` is formed
  correctly, but codegen's qualified-name **suffix** resolution maps the part
  after the last `.` through a name table to `rt_string_char_code_at`, which
  fails closed with 0 on a non-text receiver.

Likely sites (name tables keyed on the method suffix, no receiver check):
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` (~:3450-3520,
  `if let Some(dot_pos) = func_name.rfind('.')` -> `match method_part`)
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` (~:1788+,
  `let runtime_func = match method`)

Related prior filing: `codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`
covers the erased-receiver half of this; this row is the TYPED-receiver half,
which that doc's fix does not reach.

## Scope not established

Only `char_code_at` was measured. The class probe round-trips 20 builtin names
and the other 19 pass, but the probe uses a single `(i64) -> i64` shape and does
not vary arity or argument type, so a same-named user method with a different
signature may fail for names that pass here. A census of user-defined methods in
the tree whose names collide with the codegen name tables has NOT been done.

## Regression coverage (already in tree)

`test/01_unit/compiler/codegen/probe_builtin_name_collision_arg_transport_jit.spl`
checks this case on a dedicated `KNOWN-OPEN` verdict line
(`BUILTIN_NAME_COLLISION KNOWN-OPEN COUNT: 1`), asserted by
`test/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.spl`.
That count must drop to 0 when this is fixed, and the spec fails if a NEW
known-open appears — so this cannot be silently dropped or silently grow.

## Fix direction

Gate each suffix-table substitution on the receiver's static type actually being
the builtin the helper belongs to (text / array / dict), exactly as
`lowering_expr_method.rs` now gates `push`/`append` and already gated
`index_of` on `receiver_is_array`. Fall through to normal name resolution when
the receiver is a user type that defines the method.
