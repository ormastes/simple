# EasyFix Auto-Fix System Specification
*Source:* `test/feature/app/easy_fix_spec.spl`

## Overview



**Difficulty:** 3/5

## Overview

The EasyFix system provides machine-applicable fixes for diagnostics (errors,
warnings, info). It integrates with compilation, linting, and an interactive
prompt mode. Each fix has a confidence level (Safe, Likely, Uncertain) that
determines whether it can be auto-applied.

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

## Usage

    
    ```simple
    ```
    

## Behavior

### EasyFix Data Structures

## Core Data Model

    Validates the EasyFix, Replacement, and FixConfidence types
    that form the foundation of the auto-fix system.

### When FixConfidence enum

### Scenario: Confidence Levels

        Three levels of confidence determine auto-apply behavior:
        Safe (auto), Likely (review), Uncertain (human required).

- has Safe level
- has Likely level
- has Uncertain level
- Safe != Likely
- Safe != Uncertain
- Likely != Uncertain

### When Replacement creation

### Scenario: Text Replacement Records

        Each replacement specifies a file, byte span, and new text.

- creates a replacement with all fields
- creates a zero-length insertion
- creates a deletion (empty new_text)
- formats for display

### When EasyFix creation

### Scenario: Building Fix Objects

        EasyFix objects aggregate replacements with metadata.

- creates an empty fix
- adds replacements
- adds multiple replacements
- reports safe confidence
- reports non-safe for Likely
- reports non-safe for Uncertain
- formats confidence as string

### FixApplicator Engine

## Fix Application Logic

    Tests the core engine that applies text replacements to source files,
    including sorting, conflict detection, and multi-file support.

### When single replacement

### Scenario: Applying One Fix

        The simplest case: one replacement in one file.

- replaces text at the beginning
- replaces text at the end
- replaces text in the middle
- inserts text (zero-length span)
- deletes text (empty new_text)

### When multiple non-overlapping replacements

### Scenario: Multiple Fixes in One File

        When multiple fixes target different parts of the same file,
        they must be sorted and applied from end-to-start.

- applies two fixes in same file
- applies three fixes preserving order

### When conflicting replacements

### Scenario: Overlapping Spans

        When two replacements overlap in the same file, the applicator
        must detect the conflict and return an error.

- detects overlapping spans

### When multi-file fixes

### Scenario: Fixes Across Multiple Files

        Fixes can span multiple files; each file is processed independently.

- applies fixes to different files

### When missing file

### Scenario: File Not in Source Registry

        If a replacement references a file not in the source registry,
        an error is returned.

- returns error for missing file

### Fix Filtering

## Filtering Fixes by Criteria

    Tests confidence-based and ID-based filtering of fix collections.

### When confidence filtering

### Scenario: Filter by Confidence Level

        Only fixes meeting the minimum confidence threshold are included.

- Safe filter returns only safe fixes
- Likely filter returns safe and likely
- Uncertain filter returns all
- returns empty list when no fixes match

### When ID prefix filtering

### Scenario: Filter by Fix ID

        Select fixes whose IDs start with a given prefix.

- filters by prefix
- returns empty when no match
- matches exact prefix

### FixReport

## Fix Application Reporting

    After fixes are applied, a report summarizes what was done.

### When empty report

- starts with zero counts

### When report formatting

- formats dry-run report
- formats applied report

### Lint-EasyFix Integration

## Integration with Lint System

    Tests that lint diagnostics can carry EasyFix data and that
    the fix hint and easy_fix fields work together.

### When Lint with EasyFix

- creates lint with easy_fix
- creates lint without easy_fix

### When LintResult with EasyFix

- reports has_easy_fix true when present
- reports has_easy_fix false when absent
- includes fix info in formatted output

### EasyFix Edge Cases

## Edge Cases and Boundary Conditions

    Tests unusual inputs and boundary conditions in the fix system.

### When empty inputs

- handles empty fix list
- handles fix with no replacements

### When replacement at file boundaries

- replaces entire file content
- inserts at beginning of file
- appends at end of file

### When replacement size changes

- handles replacement longer than original
- handles replacement shorter than original

### When adjacent replacements

- applies adjacent non-overlapping fixes


