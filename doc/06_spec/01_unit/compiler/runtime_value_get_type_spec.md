# Runtime Value.get_type aggregate arity

Source: `test/01_unit/compiler/runtime_value_get_type_spec.spl`.

| Scenario | Assertion | Evidence |
| --- | --- | --- |
| Aggregate arity | Empty/populated structs map to struct; absent/tuple/record enum payloads map to enum | Native production projection PASS |
| Controls | Int maps to I64; nil has no MIR type; wrong opaque kind rejected | Native production projection PASS |

The companion real-import SSpec is **UNRUN**. The native projection copies 125
actual production declarations plus the production methods; it checks the
focused behavior but does not qualify import resolution or a bootstrap phase.
See `doc/08_tracking/bug/runtime_value_get_type_pattern_arity_2026_11_14.md`.
