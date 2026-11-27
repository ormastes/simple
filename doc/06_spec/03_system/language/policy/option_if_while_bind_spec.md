# `if val` / `while val` bind the Option payload

**Spec:** `test/03_system/language/policy/option_if_while_bind_spec.spl` (+ `option_if_while_bind_staged_spec.spl`, tagged in-development)
**Requirement:** typed if val / while val on Option<T> binds the payload (val is T)
**Group:** diag

| Scenario | Status | File |
|----------|--------|------|
| binds the payload as T | passing | option_if_while_bind_spec.spl |
| takes else for None | passing | option_if_while_bind_spec.spl |
| binds a text payload usable as text | passing | option_if_while_bind_spec.spl |
| iterates while Some and binds the payload | in-development | option_if_while_bind_staged_spec.spl |
| does not enter the body for an immediately-None source | in-development | option_if_while_bind_staged_spec.spl |
| gives the semantic checker no diagnostics for if val over i64? | in-development | option_if_while_bind_staged_spec.spl |

Passing: 3; in-development: 3.
