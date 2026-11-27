# `nil` accepted only inside `unsafe:`

**Spec:** `test/03_system/language/policy/nil_unsafe_only_spec.spl` (+ `nil_unsafe_only_staged_spec.spl`, tagged in-development)
**Requirement:** nil only in unsafe (lint NIL-UNSAFE-001; semantic checker)
**Group:** diag

| Scenario | Status | File |
|----------|--------|------|
| flags nil outside unsafe with a pointer to None | passing | nil_unsafe_only_spec.spl |
| accepts nil inside an unsafe block | passing | nil_unsafe_only_spec.spl |
| accepts None in safe code | passing | nil_unsafe_only_spec.spl |
| diagnoses case None over an i64 scrutinee | passing | nil_unsafe_only_spec.spl |
| gives the nil spelling a NAMED E-TYPE-NIL-COMPARE diagnostic | passing | nil_unsafe_only_spec.spl |
| accepts case None over a genuine Option | in-development | nil_unsafe_only_staged_spec.spl |
| gives case None on i64 a named E-TYPE-* code | in-development | nil_unsafe_only_staged_spec.spl |
| reports nil outside unsafe from the semantic checker, not only the lint | in-development | nil_unsafe_only_staged_spec.spl |

Passing: 5; in-development: 3.
