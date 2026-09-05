# `pub` rejected as an identifier but absent from the reserved-keyword list

**RESOLVED 2026-08-17** — option (a): `pub` is now documented as reserved in
`doc/07_guide/quick_reference/syntax_quick_reference.md` (new "Reserved
keywords that cannot be used as identifiers" line) and appended to the
reserved-keyword list in `.claude/rules/language.md`. Regression specs (both
green): `test/01_unit/doc/reserved_keyword_pub_documented_spec.spl` (repro +
full-set generalization) and its mirror
`test/unit/doc/reserved_keyword_pub_documented_spec.spl`.

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

---

## RESOLVED 2026-08-17 — option (a) taken, documented

Decision: `pub` stays a reserved word (it is a visibility modifier token in the
lexer keyword table at `src/compiler_rust/parser/src/lexer/identifiers.rs:172`,
`"pub" => TokenKind::Pub`); the gap was purely documentation.

Fix: `doc/07_guide/quick_reference/syntax_quick_reference.md` now carries a
**Reserved Words** section listing all 124 lexer keywords verbatim, extracted
mechanically from that table, plus an explicit call-out of the non-obvious
entries (`pub`, `move`, `examples`, `result`, `style`, `grid`, `city`, `music`,
`common`, `context`, `schema`, `slice`, `vec`, `outline`, `handle_pool`,
`feature`, `given`, `to`, `by`, `on`, `in`, `is`, `new`, `gen`) and the
"error surfaces at the use site, not the declaration" explanation that made
this read as a parser bug.

Also recorded there: the `See also` link to
`doc/06_spec/app/compiler/modules/grammar/keyword_reference.md` was dangling —
that generated file does not exist in the tree — so the new section is the
authoritative list until the generator is re-run.

This note also documents the same-family records
`move_identifier_rejected_as_expression_2026-08-15.md` and
`examples_identifier_rejected_in_named_argument_position_2026-08-10.md`; those
remain OPEN as *behaviour* requests (make the tokens contextual), but the
"undocumented" half of all three is now closed.
