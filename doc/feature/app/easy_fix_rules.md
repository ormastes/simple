# EasyFix Rules Specification
*Source:* `test/feature/app/easy_fix_rules_spec.spl`

## Overview



**Difficulty:** 3/5

## Overview

Intensive tests for all 9 EasyFix rules. Each rule is tested with real
code snippets, edge cases, and round-trip verification.

## Rules Tested

| # | Rule | Confidence |
|---|------|------------|
| 1 | print_in_test_spec | Likely |
| 2 | unnamed_duplicate_typed_args | Uncertain |
| 3 | resource_leak | Uncertain |
| 4 | sspec_missing_docstrings | Safe |
| 5 | sspec_manual_assertions | Likely |
| 6 | non_exhaustive_match | Safe |
| 7 | typo_suggestion (Levenshtein) | Likely |
| 8 | parser_contextual_keyword | Safe |
| 9 | type_mismatch_coercion | Likely |

## Behavior

### Rule: print_in_test_spec

## print_in_test_spec

    Detects `print()` calls in test spec files and suggests replacing
    with `expect()` assertions.

### When basic detection

### Scenario: Basic print() Detection

        Simple print() calls in spec files should be flagged.

- detects print() in spec file
- detects print with string arg
- detects print with expression
- detects multiple prints
- generates correct replacement
- preserves indentation

### When non-spec files

### Scenario: Non-spec Files Ignored

        print() in regular (non-spec) files should not be flagged.

- ignores print in regular .spl files
- ignores print in non-spl files

### When edge cases

### Scenario: Edge Cases

        Unusual inputs and boundary conditions.

- handles empty file
- handles file with only comments
- has Likely confidence

### Rule: unnamed_duplicate_typed_args

## unnamed_duplicate_typed_args

    Detects function signatures with duplicate type-only parameters
    and suggests adding distinct names.

### When basic detection

### Scenario: Duplicate Type-Only Parameters

        Functions with params like (Int, Int) should get named params.

- detects fn with two same types
- generates named params
- detects three same types

### When no false positives

### Scenario: Named Parameters Not Flagged

        Functions with properly named params should not be flagged.

- ignores named params
- ignores single type-only param
- ignores different types

### When edge cases

### Scenario: Edge Cases

- handles empty file
- handles me methods
- handles static fn
- has Uncertain confidence

### Rule: resource_leak

## resource_leak

    Detects resource allocations not wrapped in `with` blocks.

### When basic detection

### Scenario: Unwrapped Resource Allocation

- detects val x = open(...)
- detects File.open
- detects connect
- generates with block

### When no false positives

### Scenario: Already Wrapped Resources

- ignores non-resource assignments
- ignores var assignments

### When edge cases

### Scenario: Edge Cases

- handles empty file
- has Uncertain confidence

### Rule: sspec_missing_docstrings

## sspec_missing_docstrings

    Detects describe/context blocks without docstrings and adds templates.

### When basic detection

### Scenario: Missing Docstrings

- detects describe without docstring
- detects context without docstring
- generates docstring template

### When no false positives

### Scenario: Blocks With Docstrings

- ignores describe with docstring
- ignores non-spec files

### When edge cases

### Scenario: Edge Cases

- handles empty file
- has Safe confidence

### Rule: sspec_manual_assertions

## sspec_manual_assertions

    Detects `if cond: fail()` patterns and suggests `expect()`.

### When basic detection

### Scenario: Manual Assertions

- detects if x: fail()
- detects if not x: fail()
- generates expect for positive condition
- generates expect for negated condition
- detects multiple manual assertions

### When no false positives

### Scenario: Non-matching Patterns

- ignores if without fail
- ignores non-spec files

### When edge cases

### Scenario: Edge Cases

- handles empty file
- has Likely confidence
- preserves indentation

### Rule: non_exhaustive_match

## non_exhaustive_match

    Detects match blocks without catch-all `case _:` arm.

### When basic detection

### Scenario: Missing Catch-All Arm

- detects match without case _
- generates catch-all arm with todo

### When no false positives

### Scenario: Exhaustive Matches

- ignores match with case _

### When edge cases

### Scenario: Edge Cases

- handles empty file
- has Safe confidence

### Rule: typo_suggestion

## typo_suggestion

    Uses Levenshtein distance to suggest corrections for misspelled identifiers.

### When Levenshtein distance

### Scenario: Distance Calculation

- returns 0 for identical strings
- returns length for empty string
- returns 1 for single insertion
- returns 1 for single deletion
- returns 1 for single substitution
- returns 2 for two edits
- handles completely different strings
- handles single character strings
- handles both empty

### When typo fix suggestion

### Scenario: Suggesting Corrections

- suggests close match
- returns None for no close match
- has Likely confidence
- picks closest match

### Rule: parser_contextual_keyword

## parser_contextual_keyword

    Detects misordered keywords in function declarations and suggests
    the correct order.

### When async static reorder

### Scenario: async static fn → static async fn

- detects async static fn
- generates correct reorder
- has Safe confidence

### When static pub reorder

### Scenario: static pub fn → pub static fn

- detects static pub fn
- generates pub static fn

### When pub async static reorder

### Scenario: pub async static fn → pub static async fn

- detects pub async static fn
- generates pub static async fn

### When no false positives

### Scenario: Correct Keyword Order

- ignores correct static async fn
- ignores plain fn
- ignores pub static fn

### When edge cases

### Scenario: Edge Cases

- handles empty file
- handles indented keywords

### Rule: type_mismatch_coercion

## type_mismatch_coercion

    Suggests type coercion methods for common type mismatches.

### When coercion suggestions

### Scenario: Common Type Conversions

- suggests .to_string() for Int to String
- suggests .to_string() for Float to String
- suggests .to_string() for Bool to String
- suggests .to_int() for Float to Int
- suggests .to_float() for Int to Float
- suggests != 0 for Int to Bool

### When no coercion available

### Scenario: Unknown Type Pairs

- returns None for unknown type pair
- returns None for same types

### When fix metadata

### Scenario: Fix Properties

- has Likely confidence
- inserts at correct position

### check_all_rules integration

## Master Rule Runner

    Tests that check_all_rules correctly aggregates fixes from all rules.

### When aggregation

### Scenario: Multiple Rules Fire

- returns empty for clean file
- collects fixes from multiple rules
- collects spec-related fixes for spec files

### When no duplicates

### Scenario: Rules Don't Overlap

- each fix has unique ID

### Round-trip fix verification

## Round-Trip Tests

    Apply a fix, then re-check: the issue should be gone.

### When parser_contextual_keyword round-trip

### Scenario: Fix → Re-check → Clean

- fixing async static fn clears the warning

### When print_in_test_spec round-trip

### Scenario: Fix print → Re-check → No print warning

- fixing print clears the warning

### FixApplicator with shared rules

## Integration: Rules + Applicator

    Tests that fixes from rules can be applied via FixApplicator.

### When apply rule fixes

### Scenario: End-to-end fix application

- applies parser keyword fix
- applies multiple rule fixes without conflict


