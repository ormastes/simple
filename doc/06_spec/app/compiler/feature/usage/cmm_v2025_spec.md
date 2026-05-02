# CMM v2025 Version Support

Tests for CMM v2025 version support and command database updates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | In Progress |
| Source | `test/feature/usage/cmm_lsp/cmm_v2025_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for CMM v2025 version support and command database updates.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/cmm_lsp/cmm_v2025/result.json` |

## Scenarios

- config_for_version recognizes 2025
- V2025 has all features
- V2013 does not have V2025 features
- V2012 does not have V2025 or V2013 features
- Latest has all features
- Lua commands are in database
- I2C commands are in database
- Object API commands are in database
- API lock commands are in database
- Lua commands have min_version 2025
- Lua group has multiple commands
- ObjectAPI group has multiple commands
- completion suggests Lua commands
- parses Lua commands without errors
- parses Object API commands
- parses I2C commands
