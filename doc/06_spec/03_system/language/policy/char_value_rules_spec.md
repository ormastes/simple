# Char Value Rules

> A char is never falsy, never a surrogate, never equal to an int.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Requirement | ADR-005 (scalar value type, no implicit int conversion; Decision.4) |
| Source | `test/03_system/language/policy/char_value_rules_spec.spl`, `char_value_rules_in_dev_spec.spl` |
| Generator | hand-written (spipe-docgen not run) |

## Scenarios

| # | Scenario | Status |
|---|----------|--------|
| 1 | A digit char is not falsy | passing |
| 2 | A NUL char is not falsy | passing |
| 3 | A char is never equal to its code point | passing |
| 4 | `ord()` is the int view | passing |
| 5 | An astral char stays one scalar | passing |
| 6 | `char.from_code(0xD800)` rejected (interpreter) | in-development |
| 7 | `char.from_code(0xD800)` rejected (JIT) | in-development |
