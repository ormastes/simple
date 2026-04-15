# Architecture Check Error Cases

Tests failure paths and edge cases in the architecture validation system. Covers boundary conditions for string trimming, pattern list parsing, import pattern matching with glob-style wildcards, allow/deny rule evaluation, import statement extraction from source content, and module path resolution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ARCH-001 |
| Category | Tooling |
| Status | Active |
| Source | `test/feature/usage/arch_check_error_cases_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests failure paths and edge cases in the architecture validation system.
Covers boundary conditions for string trimming, pattern list parsing,
import pattern matching with glob-style wildcards, allow/deny rule evaluation,
import statement extraction from source content, and module path resolution.

## Syntax

```simple
val result = _match_pattern("core/lexer", "core/*")
val allowed = _is_import_allowed("core/ast", rule)
```
Arch Check Error Cases - Negative/Edge Path Tests

Tests failure paths and edge cases in architecture validation:
- empty/degenerate inputs to pattern matching
- pattern boundary conditions
- import parsing edge cases
- rule evaluation with empty allow/deny lists

Feature: 8 (Architecture Validation)
Source: src/app/cli/arch_check.spl

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/arch_check_error_cases/result.json` |

## Scenarios

- handles already-trimmed string unchanged
- handles empty string
- handles string of only spaces
- handles string of only tabs
- handles single character
- handles string with tab and spaces
- returns empty list for empty brackets
- returns empty list for missing brackets
- returns empty list for empty input string
- parses single quoted pattern
- parses single item with double quotes
- ignores whitespace around patterns
- empty pattern does not match non-empty import
- empty import does not match non-empty pattern
- empty import matches empty pattern exactly
- /** suffix matches any subpath of prefix
- pattern exact does not match import with extra segment
- /* does not match two levels deep
- /* matches single level sub-path
- prefix match requires slash boundary
- exact match succeeds for identical strings
- pattern with /** matches direct child
- import allowed when both allow and deny lists are empty
- import denied when not in non-empty allow list
- import allowed when in allow list and deny list is empty
- import denied when matched by deny pattern even if in allow list
- import allowed when in allow but not in deny
- returns empty list for empty content
- returns empty list for content with no use statements
- ignores comment lines starting with #
- strips trailing dot from module path
- converts dot notation to slash notation
- returns __init__.spl when init file is directly under root with no subdir
- handles path not under root unchanged
- empty module path matches any file
- file at exact module boundary matches
- file outside module boundary does not match
- file with similar prefix but different module does not match
- returns false for empty content
- returns true when arch keyword appears in comment because parser has no comment awareness
- returns empty allow and deny for arch block with no imports section
- parses arch block with empty allow list
- parses arch block with empty deny list
