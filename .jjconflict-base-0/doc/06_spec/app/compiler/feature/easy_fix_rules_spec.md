# Easy Fix Rules Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/easy_fix_rules_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 94 |
| Active scenarios | 94 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/app/easy_fix_rules/result.json` |

## Scenarios

- detects print() in spec file
- detects print with string arg
- detects print with expression
- detects multiple prints
- generates correct replacement
- preserves indentation
- ignores print in regular .spl files
- ignores print in non-spl files
- handles empty file
- handles file with only comments
- has Likely confidence
- detects fn with two same types
- generates named params
- detects three same types
- ignores named params
- ignores single type-only param
- ignores different types
- handles empty file
- handles me methods
- handles static fn
- has Uncertain confidence
- detects val x = open(...)
- detects File.open
- detects connect
- generates with block
- ignores non-resource assignments
- ignores var assignments
- handles empty file
- has Uncertain confidence
- detects describe without docstring
- detects context without docstring
- generates docstring template
- ignores describe with docstring
- ignores non-spec files
- handles empty file
- has Safe confidence
- detects if x: fail()
- detects if not x: fail()
- generates expect for positive condition
- generates expect for negated condition
- detects multiple manual assertions
- ignores if without fail
- ignores non-spec files
- handles empty file
- has Likely confidence
- preserves indentation
- detects match without case _
- generates catch-all arm with todo
- ignores match with case _
- handles empty file
- has Safe confidence
- returns 0 for identical strings
- returns length for empty string
- returns 1 for single insertion
- returns 1 for single deletion
- returns 1 for single substitution
- returns 2 for two edits
- handles completely different strings
- handles single character strings
- handles both empty
- suggests close match
- returns None for no close match
- has Likely confidence
- picks closest match
- detects async static fn
- generates correct reorder
- has Safe confidence
- detects static pub fn
- generates pub static fn
- detects pub async static fn
- generates pub static async fn
- ignores correct static async fn
- ignores plain fn
- ignores pub static fn
- handles empty file
- handles indented keywords
- suggests .to_string() for Int to String
- suggests .to_string() for Float to String
- suggests .to_string() for Bool to String
- suggests .to_int() for Float to Int
- suggests .to_float() for Int to Float
- suggests != 0 for Int to Bool
- returns None for unknown type pair
- returns None for same types
- has Likely confidence
- inserts at correct position
- returns empty for clean file
- collects fixes from multiple rules
- collects spec-related fixes for spec files
- each fix has unique ID
- fixing async static fn clears the warning
- fixing print clears the warning
- applies parser keyword fix
- applies multiple rule fixes without conflict
