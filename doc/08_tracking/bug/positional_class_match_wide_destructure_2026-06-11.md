# Bug: positional class/struct pattern match silently no-matches (interpreter) and SIGSEGVs (cranelift)

- **Date:** 2026-06-11
- **Status:** open (workaround applied at the one known production call site)
- **Severity:** high — silent wrong behavior in interpreted mode, crash in compiled mode

## Symptom

`match obj: case ClassName(a, b, c):` over a **class/struct** value:

- **Interpreter (Rust seed):** the arm silently does not match — no error, no
  output, exit 0. Verified with a 3-field struct and a 20-field struct
  (`tmp/site12/smallmatch.spl`, `tmp/site12/bigmatch.spl`).
- **Cranelift-compiled:** SIGSEGV at the match (verified by native-building
  `bigmatch.spl` with the release seed and running in docker).

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

## Fix direction

Either implement positional field binding for class/struct patterns in both
the seed interpreter and cranelift lowering, or reject the pattern at
parse/type-check time with a diagnostic ("positional patterns are only
supported for enum variants — use `case P(x: x, y: y)` or field access").
Silent no-match is the worst of the options.
