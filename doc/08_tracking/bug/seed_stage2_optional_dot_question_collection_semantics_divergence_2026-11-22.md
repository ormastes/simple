# Seed vs Stage 2 divergence on .? for collection optionals

- **Date:** 2026-11-22
- **Status:** open
- **Severity:** P2

## Symptom

For collection values, `not xs.?` means "absent OR empty", which differs from `xs.is_none()`. The seed and Stage 2 disagree on this, so code that passes under one can change behavior under the other.

## Evidence

This is the #10717 regression, fixed in #10743 (11 sites). A doc warning was added to `doc/07_guide/quick_reference/syntax_quick_reference.md`. The seed/Stage 2 disagreement was flagged earlier as an open item and is recorded here.

## Repro

Evaluate `not xs.?` and `xs.is_none()` on an empty (non-nil) collection under the seed and under Stage 2, and compare.

## Workaround

Use `is_none()` when only absence is meant; do not write `not <collection-optional>.?`.

## Fix direction

Align seed and Stage 2 semantics, and add a lint rule against `not <collection-optional>.?`.

## Lint rule

Lint rule `not_dot_question` (code `NDQ001`, warning) flags every syntactic `not <expr>.?` and asks the author to check intent (`is_none()` vs `is_none() or unwrap().is_empty()`). Lint has no type info, so it is not limited to collections. Implementation: `src/compiler/35.semantics/lint/not_dot_question.spl`; spec `test/01_unit/compiler/lint/not_dot_question_spec.spl`. Population at introduction: about 1250 sites in 308 `src/**/*.spl` files (grep estimate, not converted). The seed/Stage 2 semantic divergence itself remains open.
