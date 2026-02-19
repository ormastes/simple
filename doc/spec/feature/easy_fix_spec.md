# EasyFix Auto-Fix System Specification

**Feature ID:** #2200-2210 | **Category:** Tooling | **Difficulty:** 3/5 | **Status:** Implemented

_Source: `test/feature/app/easy_fix_spec.spl`_

---

## Overview

The EasyFix system provides machine-applicable fixes for diagnostics (errors,
warnings, info). It integrates with compilation, linting, and an interactive
prompt mode. Each fix has a confidence level (Safe, Likely, Uncertain) that
determines whether it can be auto-applied.

## Syntax

```simple
# Fix flags on CLI:
# simple lint --fix           Apply safe fixes
# simple lint --fix-all       Apply all fixes
# simple lint --fix-dry-run   Preview fixes
# simple lint --fix-interactive  Prompt per fix
# simple fix file.spl         Standalone fix command
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| EasyFix | A machine-applicable fix with ID, description, replacements, confidence |
| Replacement | A text substitution: file, span (start/end), new_text |
| FixConfidence | Safe (auto-apply), Likely (review), Uncertain (human review) |
| FixApplicator | Engine that sorts, validates, and applies replacements |
| FixReport | Summary of applied/skipped fixes and modified files |

## Behavior

- Fixes are attached to diagnostics via `easy_fix: Option<EasyFix>`
- Replacements are applied from end-to-start to preserve byte offsets
- Overlapping spans are detected and rejected as conflicts
- Confidence levels control which fixes are auto-applied
- Interactive mode prompts: [y]es / [n]o / [a]ll / [q]uit

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 50 |

## Test Structure

### EasyFix Data Structures

#### FixConfidence enum

- ✅ has Safe level
- ✅ has Likely level
- ✅ has Uncertain level
- ✅ Safe != Likely
- ✅ Safe != Uncertain
- ✅ Likely != Uncertain
#### Replacement creation

- ✅ creates a replacement with all fields
- ✅ creates a zero-length insertion
- ✅ creates a deletion (empty new_text)
- ✅ formats for display
#### EasyFix creation

- ✅ creates an empty fix
- ✅ adds replacements
- ✅ adds multiple replacements
- ✅ reports safe confidence
- ✅ reports non-safe for Likely
- ✅ reports non-safe for Uncertain
- ✅ formats confidence as string
### FixApplicator Engine

#### single replacement

- ✅ replaces text at the beginning
- ✅ replaces text at the end
- ✅ replaces text in the middle
- ✅ inserts text (zero-length span)
- ✅ deletes text (empty new_text)
#### multiple non-overlapping replacements

- ✅ applies two fixes in same file
- ✅ applies three fixes preserving order
#### conflicting replacements

- ✅ detects overlapping spans
#### multi-file fixes

- ✅ applies fixes to different files
#### missing file

- ✅ returns error for missing file
### Fix Filtering

#### confidence filtering

- ✅ Safe filter returns only safe fixes
- ✅ Likely filter returns safe and likely
- ✅ Uncertain filter returns all
- ✅ returns empty list when no fixes match
#### ID prefix filtering

- ✅ filters by prefix
- ✅ returns empty when no match
- ✅ matches exact prefix
### FixReport

#### empty report

- ✅ starts with zero counts
#### report formatting

- ✅ formats dry-run report
- ✅ formats applied report
### Lint-EasyFix Integration

#### Lint with EasyFix

- ✅ creates lint with easy_fix
- ✅ creates lint without easy_fix
#### LintResult with EasyFix

- ✅ reports has_easy_fix true when present
- ✅ reports has_easy_fix false when absent
- ✅ includes fix info in formatted output
### EasyFix Edge Cases

#### empty inputs

- ✅ handles empty fix list
- ✅ handles fix with no replacements
#### replacement at file boundaries

- ✅ replaces entire file content
- ✅ inserts at beginning of file
- ✅ appends at end of file
#### replacement size changes

- ✅ handles replacement longer than original
- ✅ handles replacement shorter than original
#### adjacent replacements

- ✅ applies adjacent non-overlapping fixes

