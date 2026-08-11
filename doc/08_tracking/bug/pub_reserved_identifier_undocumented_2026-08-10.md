# `pub` rejected as an identifier but absent from the reserved-keyword list

**Found:** 2026-08-10, wave C5 spec authoring.

## Symptom
```
val pub = block_key_publish(...)   # parse error: "expected pattern, found Pub"
```
`pub` lexes as a keyword token everywhere, so it cannot be bound as a variable
name — but the documented reserved-keyword list
(`doc/07_guide/quick_reference/syntax_quick_reference.md`) does not include it,
so the failure reads as a parser bug rather than a rule.

## Expected
Either (a) document `pub` in the reserved list, or (b) allow it as an
identifier in pattern position if `pub` visibility is only meaningful before
declarations.

## Unblock condition
Decision on (a) vs (b); if (a), one doc line closes this. Workaround: any other
name.
