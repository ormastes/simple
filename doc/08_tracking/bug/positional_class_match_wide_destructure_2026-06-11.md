# Bug: positional class/struct pattern match silently no-matches (interpreter) and SIGSEGVs (cranelift)

- **Date:** 2026-06-11
- **Status:** interpreter FIXED IN SEED (2026-06-12, pending redeploy); cranelift SIGSEGV still open
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
  unaffected) all green. Production workaround in `flat_ast_bridge_part1.spl`
  is still in place and does not need to be reverted.
- **Cranelift-compiled:** SIGSEGV at the match (verified by native-building
  `bigmatch.spl` with the release seed and running in docker). Still open.

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

`convert_decl_method_fn` (src/compiler/10.frontend/flat_ast_bridge_part1.spl)
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

## Remaining open

Cranelift SIGSEGV: out of scope for this fix. Cranelift codegen for positional
class patterns needs separate investigation.

## Fix direction (original, archived)

Either implement positional field binding for class/struct patterns in both
the seed interpreter and cranelift lowering, or reject the pattern at
parse/type-check time with a diagnostic ("positional patterns are only
supported for enum variants — use `case P(x: x, y: y)` or field access").
Silent no-match is the worst of the options.
