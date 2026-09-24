# Duplicate-check cosine fragmented one clone into multiple groups — 2026-07-23
## Closed 2026-09-16 — Status SOURCE FIXED; focused regression passed 12 examples 0 failures

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** SOURCE FIXED / PURE-SIMPLE QUALIFICATION PENDING

## Reproduction

The existing same-file cosine regression creates two non-overlapping functions
with renamed identifiers. The detector returned two groups for that one clone
pair instead of one group containing the two physical occurrences.

## Root cause and fix

Cosine adjacency skipped overlapping windows from the same file before scoring
them. Different similar sliding fragments therefore formed separate graph
components and each survived as a duplicate group.

Overlapping candidates now use the same cosine threshold as every other pair.
The existing component builder joins only similar fragments, while the existing
overlap collapse reduces each physical region to one occurrence and rejects
overlap-only components that collapse below two occurrences.

The focused regression also asserts that both retained occurrences belong to
the fixture file. Its temporary bootstrap-interpreter run passed 12 examples
with 0 failures. A fresh pure-Simple Stage 4 candidate must pass the complete
spec before qualification.

