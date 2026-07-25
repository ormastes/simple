# Cosine duplicate check ignored same-file fuzzy clones

**Status:** SOURCE FIXED; RUNTIME QUALIFICATION PENDING
**Severity:** P1 — renamed duplicate blocks in one file were silently omitted

## Reproduction

`build_similarity_adjacency` skipped every pair whose blocks shared a file.
Consequently cosine mode could find the same renamed functions across two files
but returned no group when those functions were in one file.

## Root fix

Same-file pairs are now skipped only when their line ranges overlap. Distinct
local blocks remain eligible, while sliding windows from one source region
cannot self-group. After overlap collapse, groups must still contain at least
two occurrences.

`test/01_unit/app/duplicate_check/detector_grouping_spec.spl` contains a
non-overlapping renamed-block positive case and an overlapping-window negative
case.

## Evidence boundary

High-capability source review passed. The deployed pure-Simple test command
segfaulted with exit 139 and no output. The bounded Rust-seed diagnostic exited
1 because the runner executed zero examples. Runtime and Stage 4 qualification
remain pending; neither result is reported as a passing test.
