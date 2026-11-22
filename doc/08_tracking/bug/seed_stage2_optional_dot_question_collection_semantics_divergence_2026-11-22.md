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
