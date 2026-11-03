# `Any` / erased escapes accepted only inside `unsafe`

**Spec:** `test/03_system/language/policy/any_unsafe_only_spec.spl`
**Requirement:** Any only in unsafe (W/E-ANY-COMPILE-001, type_erasure)
**Group:** diag

| Scenario | Status | File |
|----------|--------|------|
| warns with W-ANY-COMPILE-001 by default | passing | any_unsafe_only_spec.spl |
| errors with E-ANY-COMPILE-001 when written Any is forbidden | passing | any_unsafe_only_spec.spl |
| flags an erased [u8] escape through an Any local | passing | any_unsafe_only_spec.spl |
| accepts Any inside unsafe(capabilities: [type_erasure]) in both modes | passing | any_unsafe_only_spec.spl |
| reports nothing for concrete or generic types | passing | any_unsafe_only_spec.spl |
| Any inside plain unsafe without type_erasure is still diagnosed | passing | any_unsafe_only_spec.spl |

Passing: 6; in-development: 0.
