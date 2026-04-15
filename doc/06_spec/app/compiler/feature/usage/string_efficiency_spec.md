# String Operation Efficiency Specification

Tests that string operations in the CMM LSP toolchain produce correct results after being rewritten from O(n²) character-by-character concatenation to O(n log n) segment-based approaches. Covers: escape_json, json_array, json_object, json_get_string, json_get_int, split_lines, lex_string_literal, to_upper_cmm, and join_parts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-STR-EFF |
| Category | Tooling |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/feature/usage/cmm_lsp/string_efficiency_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests that string operations in the CMM LSP toolchain produce correct results
after being rewritten from O(n²) character-by-character concatenation to
O(n log n) segment-based approaches. Covers: escape_json, json_array,
json_object, json_get_string, json_get_int, split_lines, lex_string_literal,
to_upper_cmm, and join_parts.

These are correctness tests that verify the optimized implementations match
the behavior of the original naive implementations. They include large-input
cases that would have been noticeably slow with the old O(n²) approach.

## Batch String Joining

    The core helper used by all optimized string operations.
    Uses recursive batch-of-8 concatenation for O(n log n) performance.

## Case-Insensitive CMM Keyword Matching

    Tests the optimized uppercase conversion that uses a fast-path check
    and array-join for the slow path.

## JSON String Escaping

    Tests the optimized escape_json that uses segment collection instead
    of character-by-character concatenation.

## JSON Array Builder

    Tests the optimized json_array that collects segments instead of
    repeatedly concatenating.

## JSON Object Builder

    Tests the optimized json_object.

## Line Splitting

    Tests the split_lines function used by the lexer.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cmm_lsp/string_efficiency/result.json` |

## Scenarios

- joins empty array
- joins single element
- joins two elements
- joins three elements
- joins four elements
- joins 5 elements
- joins 8 elements — exact batch
- joins 9 elements — batch + remainder
- joins 16 elements — two full batches
- joins 100 single-char parts
- joins 500 single-char parts
- joins segments of varying length
- joins with empty segments
- returns uppercase string unchanged
- returns uppercase keyword unchanged
- returns numbers/symbols unchanged
- converts lowercase to uppercase
- converts mixed case
- converts all lowercase keyword
- converts long keyword
- converts single char
- handles empty string
- preserves underscores and digits
- converts 200 lowercase chars
- returns plain string unchanged
- returns empty string unchanged
- returns alphanumeric unchanged
- escapes backslash
- escapes double quote
- escapes newline
- escapes carriage return
- escapes tab
- escapes string with multiple specials
- escapes only-specials string
- escapes special at start
- escapes special at end
- escapes consecutive specials
- escapes 500 chars with scattered specials
- builds empty array
- builds single-element array
- builds two-element array
- builds multi-element array
- builds array of JSON strings
- builds array with 100 elements
- builds empty object
- builds single-pair object
- builds multi-pair object
- builds object with string values
- builds object with 50 pairs
- splits empty string into one empty line
- splits single line without newline
- splits two lines
- splits three lines
- splits with trailing newline — produces empty last line
- handles consecutive newlines
- handles only newlines
- splits typical CMM script
- splits 200 lines
