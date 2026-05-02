# CMM Parser V4 Fixes Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-PARSE-V4 |
| Category | Tooling |
| Status | Implemented |
| Source | `test/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/cmm_lsp/cmm_parse_v4_fixes/result.json` |

## Scenarios

- parses Data.LOAD with single continuation
- parses multi-line continuation
- parses string concat with continuation
- parses dialog.yesno with continuation
- handles commented continuation line
- parses C++ scoped name in function arg
- parses scoped symbol with backtick
- parses standalone device selector
- parses if-else with separate-line paren blocks
- parses if-else-if chain
- parses macro with dot extension
- parses macro with backslash path
- parses macro trailing dot
- parses triple question mark after assignment
- parses bare & in dialog block
- parses READ with %line format specifier
- parses dot-prefixed section name in function arg
- handles stray closing paren at top level
- handles trailing tokens after macro assignment
