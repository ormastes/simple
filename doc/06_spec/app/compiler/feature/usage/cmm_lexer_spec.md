# CMM Lexer Specification

Tests for the CMM (PRACTICE Script) lexer. Validates tokenization of all CMM lexical elements: comments, labels, macros, numbers, strings, dot commands, operators, options, file channels, and full lines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-LEX |
| Category | Tooling |
| Status | Implemented |
| Source | `test/feature/usage/cmm_lsp/cmm_lexer_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 95 |
| Active scenarios | 95 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for the CMM (PRACTICE Script) lexer. Validates tokenization of all
CMM lexical elements: comments, labels, macros, numbers, strings, dot
commands, operators, options, file channels, and full lines.

Interpreter mode: it block bodies don't execute. Tests verify that
all CMM lexer concepts are structurally valid Simple code that loads
without errors.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/cmm_lsp/cmm_lexer/result.json` |

## Scenarios

- lexes semicolon comment
- lexes double-slash comment
- lexes semicolon comment with no trailing text
- lexes double-slash comment with no trailing text
- lexes inline comment after whitespace
- lexes label at column 1
- lexes label with underscore
- lexes label with alphanumeric chars
- distinguishes label from device selector
- returns empty for empty line
- lexes simple macro ref
- lexes recursive macro ref
- lexes bare ampersand as operator when no identifier follows
- lexes bare double-ampersand as logical AND when no identifier follows
- lexes macro ref with underscore in name
- lexes hex number with lowercase 0x
- lexes hex number with uppercase 0X
- lexes hex mask with dont-care bits
- lexes hex mask with multiple dont-care bits
- lexes binary number with 0y prefix
- lexes binary mask with dont-care bits
- lexes decimal number with trailing dot
- lexes plain integer
- lexes float number
- lexes float with exponent
- lexes millisecond time literal
- lexes microsecond time literal
- lexes nanosecond time literal
- lexes second time literal
- lexes float time literal
- lexes simple string
- lexes empty string
- lexes string with escaped double quote
- lexes single character literal
- lexes lowercase char literal
- lexes simple dot command
- lexes two-level dot command
- lexes multi-level dot command
- lexes dot command with reset
- lexes equality operator
- lexes not-equal operator
- lexes less-than-or-equal
- lexes greater-than-or-equal
- lexes range-to operator
- lexes range-offset operator
- lexes range-dots operator
- lexes logical AND
- lexes logical OR
- lexes logical XOR
- lexes shift left
- lexes shift right
- lexes classic AND colon form
- lexes classic OR colon form
- lexes classic XOR colon form
- lexes plus
- lexes minus
- lexes star
- lexes percent
- lexes tilde
- lexes bang
- lexes assign
- lexes left paren
- lexes right paren
- lexes left brace
- lexes right brace
- lexes comma
- lexes option token
- lexes read option
- lexes create option
- lexes file channel 1
- lexes file channel 2
- lexes hash classic AND
- lexes hash classic OR
- lexes hash classic XOR
- lexes device selector B::
- lexes device selector E::
- lexes simple identifier
- lexes uppercase identifier
- lexes identifier with underscore
- lexes command with parameter
- lexes command with hex parameter
- lexes macro assignment
- lexes command with option
- lexes print with string
- lexes write with file channel
- lexes range expression
- lexes multi-line CMM source
- lexes empty source
- lexes source with line continuation
- lexes real-world flash script
- handles whitespace-only line
- handles tab whitespace
- preserves line numbers
- handles classic NOT operator N:
- handles slash as division when not followed by alpha
