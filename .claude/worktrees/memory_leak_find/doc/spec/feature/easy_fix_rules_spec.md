# EasyFix Rules Specification

**Feature ID:** #2211-2220 | **Category:** Tooling | **Difficulty:** 3/5 | **Status:** Implemented

_Source: `test/feature/app/easy_fix_rules_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 94 |

## Test Structure

### Rule: print_in_test_spec

#### basic detection

- ✅ detects print() in spec file
- ✅ detects print with string arg
- ✅ detects print with expression
- ✅ detects multiple prints
- ✅ generates correct replacement
- ✅ preserves indentation
#### non-spec files

- ✅ ignores print in regular .spl files
- ✅ ignores print in non-spl files
#### edge cases

- ✅ handles empty file
- ✅ handles file with only comments
- ✅ has Likely confidence
### Rule: unnamed_duplicate_typed_args

#### basic detection

- ✅ detects fn with two same types
- ✅ generates named params
- ✅ detects three same types
#### no false positives

- ✅ ignores named params
- ✅ ignores single type-only param
- ✅ ignores different types
#### edge cases

- ✅ handles empty file
- ✅ handles me methods
- ✅ handles static fn
- ✅ has Uncertain confidence
### Rule: resource_leak

#### basic detection

- ✅ detects val x = open(...)
- ✅ detects File.open
- ✅ detects connect
- ✅ generates with block
#### no false positives

- ✅ ignores non-resource assignments
- ✅ ignores var assignments
#### edge cases

- ✅ handles empty file
- ✅ has Uncertain confidence
### Rule: sspec_missing_docstrings

#### basic detection

- ✅ detects describe without docstring
- ✅ detects context without docstring
- ✅ generates docstring template
#### no false positives

- ✅ ignores describe with docstring
- ✅ ignores non-spec files
#### edge cases

- ✅ handles empty file
- ✅ has Safe confidence
### Rule: sspec_manual_assertions

#### basic detection

- ✅ detects if x: fail()
- ✅ detects if not x: fail()
- ✅ generates expect for positive condition
- ✅ generates expect for negated condition
- ✅ detects multiple manual assertions
#### no false positives

- ✅ ignores if without fail
- ✅ ignores non-spec files
#### edge cases

- ✅ handles empty file
- ✅ has Likely confidence
- ✅ preserves indentation
### Rule: non_exhaustive_match

#### basic detection

- ✅ detects match without case _
- ✅ generates catch-all arm with todo
#### no false positives

- ✅ ignores match with case _
#### edge cases

- ✅ handles empty file
- ✅ has Safe confidence
### Rule: typo_suggestion

#### Levenshtein distance

- ✅ returns 0 for identical strings
- ✅ returns length for empty string
- ✅ returns 1 for single insertion
- ✅ returns 1 for single deletion
- ✅ returns 1 for single substitution
- ✅ returns 2 for two edits
- ✅ handles completely different strings
- ✅ handles single character strings
- ✅ handles both empty
#### typo fix suggestion

- ✅ suggests close match
- ✅ returns None for no close match
- ✅ has Likely confidence
- ✅ picks closest match
### Rule: parser_contextual_keyword

#### async static reorder

- ✅ detects async static fn
- ✅ generates correct reorder
- ✅ has Safe confidence
#### static pub reorder

- ✅ detects static pub fn
- ✅ generates pub static fn
#### pub async static reorder

- ✅ detects pub async static fn
- ✅ generates pub static async fn
#### no false positives

- ✅ ignores correct static async fn
- ✅ ignores plain fn
- ✅ ignores pub static fn
#### edge cases

- ✅ handles empty file
- ✅ handles indented keywords
### Rule: type_mismatch_coercion

#### coercion suggestions

- ✅ suggests .to_string() for Int to String
- ✅ suggests .to_string() for Float to String
- ✅ suggests .to_string() for Bool to String
- ✅ suggests .to_int() for Float to Int
- ✅ suggests .to_float() for Int to Float
- ✅ suggests != 0 for Int to Bool
#### no coercion available

- ✅ returns None for unknown type pair
- ✅ returns None for same types
#### fix metadata

- ✅ has Likely confidence
- ✅ inserts at correct position
### check_all_rules integration

#### aggregation

- ✅ returns empty for clean file
- ✅ collects fixes from multiple rules
- ✅ collects spec-related fixes for spec files
#### no duplicates

- ✅ each fix has unique ID
### Round-trip fix verification

#### parser_contextual_keyword round-trip

- ✅ fixing async static fn clears the warning
#### print_in_test_spec round-trip

- ✅ fixing print clears the warning
### FixApplicator with shared rules

#### apply rule fixes

- ✅ applies parser keyword fix
- ✅ applies multiple rule fixes without conflict

