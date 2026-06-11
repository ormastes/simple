# Bug: Parser hardcodes Some/None/Ok/Err as Option/Result variant names

Status: FIXED in interpreter_patterns.rs — see fix note below

**Date:** 2026-05-30
**Severity:** High — user-defined enums with variants named Some, None, Ok, or Err fail to match in interpreter mode
**Affected modes:** Interpreter only (compiled mode not verified)
**Status:** FIXED in interpreter_patterns.rs — see fix note below

---

## Description

The parser hardcodes `case Some(...)` → `Pattern::Enum{name:"Option", variant:"Some"}`,
`case None` → `Pattern::Enum{name:"Option", variant:"None"}`,
`case Ok(...)` → `Pattern::Enum{name:"Result", variant:"Ok"}`,
`case Err(...)` → `Pattern::Enum{name:"Result", variant:"Err"}`.

When a user-defined enum (e.g., `MaybeNumber`, `ResultValue`) has variants named `Some`, `None`, `Ok`, or `Err`, the interpreter's `pattern_matches` function rejects these patterns because it checks `enum_name == "Option"` against the actual value's `enum_name` (e.g., `"MaybeNumber"`), which never matches.

## Minimal repro

```spl
enum MaybeNumber:
    Some(value: i64)
    None

impl MaybeNumber:
    fn is_some() -> bool:
        match self:
            case Some(_): true     # <- fails: pattern::Enum{name:"Option"} vs value enum_name:"MaybeNumber"
            case None: false

val v = MaybeNumber.Some(9)
print("{v.is_some()}")   # prints "nil" instead of "true"
```

Qualified patterns work: `case MaybeNumber.Some(_)` matches correctly.

## Root cause

`parser/src/parser_patterns.rs` lines 344-350:
```rust
let (enum_name, variant) = match name.as_str() {
    "Some" => ("Option".to_string(), "Some".to_string()),
    "Ok" => ("Result".to_string(), "Ok".to_string()),
    "Err" => ("Result".to_string(), "Err".to_string()),
    _ => ("_".to_string(), name.clone()),
};
```

And line 332-338 for `None`.

This causes `Pattern::Enum{name:"Option", ...}` when matching user enums.

In `interpreter_patterns.rs` line 244:
```rust
let enum_matches = enum_name == "_" || enum_name == ve;
```

`"Option" == "MaybeNumber"` → false → pattern rejected.

## Fix applied

`interpreter_patterns.rs` line 244 extended to treat "Option" and "Result" as wildcard-compatible:

```rust
let enum_matches = enum_name == "_" || enum_name == ve
    || matches!(enum_name.as_str(), "Option" | "Result");
```

The variant name check (`variant == vv`) prevents cross-variant leakage.

## Scope

- Fixes: 6/8 failures in `test/03_system/feature/language/data_structures_spec.spl`
  (enums_9, option_17, option_18, result_20, result_22, result_23)
- Does NOT fix: the parser itself — compiled mode likely still mishandles
  user enums with these variant names (out of scope for interpreter fix)
- Does NOT fix: classes_reference_types_3 (class aliasing) or strong_enums_14 (separate bugs)

## Affected tests

- `test/03_system/feature/language/data_structures_spec.spl`: enums_algebraic_data_types_9,
  option_type_17, option_type_18, result_type_20, result_type_22, result_type_23
