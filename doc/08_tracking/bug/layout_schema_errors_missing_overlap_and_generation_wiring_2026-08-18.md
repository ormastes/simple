# `layout_schema_errors` missing overlap/duplicate-name checks and never wired into generation

- Status: OPEN
- Found: 2026-08-18 (goal 4 evidence-hardening pass over the binary SSpec suites)
- Files: `src/lib/common/spec/evidence/format/layout_schema.spl`
- Regression specs (adversarial cases, asserting CURRENT unsafe behavior):
  `test/01_unit/lib/common/spec/evidence/binary_layout_schema_spec.spl`
  ("FINDING: layout_schema_errors does not catch overlapping fields",
  "FINDING: layout_schema_errors does not catch duplicate field names",
  "FINDING: layout_words/layout_compare never call layout_schema_errors ...")

## Problem

`layout_schema_errors(layout: WordLayout) -> [text]` (layout_schema.spl:84)
only checks three things per field: non-positive width, crossing a word
boundary, and exceeding `word_bits * word_count`. Two defects it does NOT
catch, both of which its sibling validator in `binary_layout.spl`
(`layout_errors`, which DOES call `fields_overlap`) does catch for the
non-declarative `BinaryLayout` model:

1. **Overlapping fields.** Two `LayoutFieldSpec`s that occupy the same bits
   within a word produce zero errors. `layout_words` packs them via
   `field_insert` in field-list order, so the later field silently clobbers
   the earlier one's bits with no diagnostic.
2. **Duplicate field names.** Two fields sharing a `name` produce zero
   errors. Consumers that look up a field diff by name (e.g.
   `WordDiff.failing_fields.contains(name)`) cannot distinguish which of the
   two actually failed.

Separately, and more seriously: **`layout_schema_errors` has zero callers
anywhere in the tree** (`grep -rn layout_schema_errors src test` finds only
its own definition). None of `layout_words`, `layout_masks`,
`layout_compare`, or `layout_render` consult it before generating expected
words / masks / diffs. Contrast with `decode_u64` in `binary_layout.spl`,
which calls `layout_errors` first and returns a `canonical_evidence_parse_error`
on any layout defect — the declarative schema has no equivalent fail-closed
gate. A malformed `WordLayout` (including the overlap/duplicate-name cases
above, and even a cross-word-boundary or out-of-range field that
`layout_schema_errors` DOES know how to detect) is generated and compared
against silently instead of failing the capture.

## Impact

A hand-authored `WordLayout` with an accidental field overlap, duplicate
name, or other defect that `layout_schema_errors` can detect produces a
`WordDiff` that looks like an ordinary pass/fail result with no indication
the layout itself is invalid — the comparator proves nothing about the
overlapping bits beyond whichever field happened to be inserted last.

## Suggested fix

- Add `fields_overlap`-equivalent and duplicate-name checks to
  `layout_schema_errors`, mirroring `binary_layout.layout_errors`.
- Wire `layout_schema_errors` into `layout_words` / `layout_compare` (at
  minimum `layout_compare`, the comparator entry point) so a malformed
  layout fails closed instead of silently generating output, matching
  `decode_u64`'s pattern.

Not fixed here — this record exists so the gap is tracked instead of
silently accepted; the adversarial specs above assert the CURRENT (unsafe)
behavior deliberately, so a future fix will need those specific assertions
updated to their corrected form.
