# Bug: positional class/struct pattern match silently no-matches (interpreter) and SIGSEGVs (cranelift)

- **Date:** 2026-06-11
- **Status:** FULLY FIXED (interpreter 2026-06-12; cranelift/JIT compiled path 2026-06-12)
- **Severity:** high — silent wrong behavior in interpreted mode, crash in compiled mode

## Symptom

`match obj: case ClassName(a, b, c):` over a **class/struct** value:

- **Interpreter (Rust seed):** the arm silently did not match — no error, no
  output, exit 0. **FIXED 2026-06-12** in `interpreter_patterns.rs` +
  `interpreter_control.rs`: positional `Pattern::Enum` over `Value::Object` now
  binds fields in class declaration order; arity mismatch is a clean no-match.
  Verified: `smallmatch.spl` prints `matched: 10 20 30`; `bigmatch.spl` prints
  `matched: first=1 last=20`. 5 regression tests in `interpreter_patterns::tests`
  (3-field, 20-field, arity mismatch, named-field unaffected, enum positional
  unaffected) all green. Production workaround in `_FlatAstBridge/convert_nodes.spl`
  is still in place and does not need to be reverted.
- **Cranelift-compiled (JIT):** printed "no match" (the `rt_enum_check_discriminant`
  call always returned false on an object pointer). **FIXED 2026-06-12** in
  `hir/lower/stmt_lowering.rs` and `hir/lower/expr/control.rs`. Verified:
  `/tmp/a3_match_probe.spl` (Point with x=10,y=20,z=30) prints `matched: 10 20 30`
  in both compiled and interpreter modes.

Enum-variant positional patterns are unaffected (pervasively used and green).

## Repro

```spl
class P:
    x: i64
    y: text
    z: bool

fn main():
    val p = P(x: 1, y: "a", z: true)
    match p:
        case P(x, y, z):
            print("SMALL x={x} y={y} z={z}")   # never prints; rc=0
```

Compiled: `simple native-build --backend cranelift smallmatch.spl -o out && out` → segfault
(20-field variant confirmed; small variant assumed same family).

## Impact found

`convert_decl_method_fn` (src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl)
destructured `Function` with a 19-slot positional `case Function(...)`. In the
stage4 self-hosted binary this made **every class-with-method check/lint run
SIGSEGV** (12th-site cluster of the stage4 chain). Rewritten to field access
2026-06-11.

## Fix applied (interpreter)

`src/compiler_rust/compiler/src/interpreter_patterns.rs`: inside the
`Pattern::Enum` branch, after the existing enum-variant matching block, added a
new block that fires when `value` is `Value::Object`. If `variant == class` (the
parser emits class-name patterns as `Pattern::Enum{name:"_", variant:ClassName}`),
look up the `ClassDef` from the `classes` map, zip the payload patterns against
the field names in declaration order, recurse via `pattern_matches`, and commit
bindings only if all sub-patterns match. Arity mismatch → `Ok(false)` (clean
no-match). `match_sequence_pattern` and all `pattern_matches` call sites in
`interpreter_control.rs` updated to pass the `classes` parameter.

## Fix applied (cranelift/compiled — 2026-06-12)

Root cause: `Pattern::Enum{name:"_", variant:"ClassName"}` in the HIR lowering
was treated as an enum variant in both the condition check and payload extraction:

1. **Condition** (`lower_pattern_condition_stmt` / `lower_pattern_condition`):
   emitted `rt_enum_check_discriminant(subject, hash(ClassName))` which always
   returns false for an object pointer → arm never matched.

2. **Payload extraction** (stmt path): emitted `rt_enum_payload` + array indexing
   which is wrong for flat-struct objects.

**Fix in `hir/lower/stmt_lowering.rs` and `hir/lower/expr/control.rs`:**

- In both `lower_pattern_condition_stmt` and `lower_pattern_condition`: before
  emitting the discriminant check, probe `self.module.types.lookup(variant)` — if
  the variant name resolves to a `HirType::Struct` (i.e. a class), return
  `Bool(true)` instead (the type system already guarantees the match at the call
  site).

- In the binding extraction block (stmt path): detect the class/struct pattern
  via the same type lookup. For each payload pattern at position `i`, emit
  `HirExprKind::FieldAccess { receiver: subject, field_index: i }` with the
  struct's own field type. Also patch `ctx.locals[local_idx].ty` to the concrete
  field type (not ANY), because the MIR lowering reads `local.ty` as
  `effective_declared_ty` for the Store instruction — leaving it as ANY causes
  the downstream type system to mis-format i64 fields (prints as float zero).

**Regression tests added** in `hir/lower/tests/control_flow_tests.rs`:
- `test_positional_class_pattern_match_lowering`: verifies `Bool(true)` condition
  and `FieldAccess` bindings for `case Point(a, b, c)`.
- `test_enum_variant_pattern_condition_still_uses_discriminant`: guards that
  enum variants still use `rt_enum_check_discriminant`.

## Remaining open

None. Both interpreter and cranelift paths are fixed and verified.
