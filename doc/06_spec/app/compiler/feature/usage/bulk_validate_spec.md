# Bulk Validate Path Handling Specification

Tests for path normalization, dot-directory handling, file extension detection, and CMM file identification in the bulk validator. Covers the bug where rt_dir_list() callers could not handle paths containing `.`, `..`, or double slashes, and the heuristic that mistakenly treated directories as files (or vice versa).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-BULK-PATH |
| Category | Tooling |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/feature/usage/cmm_lsp/bulk_validate_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 80 |
| Active scenarios | 80 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for path normalization, dot-directory handling, file extension detection,
and CMM file identification in the bulk validator. Covers the bug where
rt_dir_list() callers could not handle paths containing `.`, `..`, or
double slashes, and the heuristic that mistakenly treated directories
as files (or vice versa).

## Key Concepts

| Concept | Description |
|---------|-------------|
| normalize_path | Resolves `.`, `..`, double slashes, trailing slashes |
| is_likely_directory | Heuristic: no extension = directory, dotfile = skip |
| is_cmm_file | Case-insensitive `.cmm` extension check |
| collect_cmm_files | Recursive directory traversal with dot-dir safety |

## Path Normalization

    Validates that normalize_path correctly resolves `.`, `..`, double
    slashes, and trailing slashes. This is the core fix for the dot-dir bug.

### Bug Reproduction

        These are the exact path patterns that triggered the original bug
        where collect_cmm_files would pass un-normalized paths to rt_dir_list.

## CMM File Detection

    Validates case-insensitive `.cmm` extension matching without O(n²)
    string conversion.

## Directory Detection Heuristic

    Validates that the heuristic correctly distinguishes directories from files,
    and properly handles hidden dotfiles/dotdirs.

### Hidden Entry Handling (Bug Fix)

        Previously, `.gitignore` was detected as having an extension and
        not recursed. Hidden directories like `.svn` were also not recursed.
        The fix is to return false for all hidden entries so they are neither
        recursed into nor collected as CMM files.

## Substring Search

    Validates the O(n) contains function used for error categorization.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cmm_lsp/bulk_validate/result.json` |

## Scenarios

- returns identity for clean paths
- returns identity for relative clean paths
- returns identity for root
- resolves single dot to current dir
- resolves leading dot-slash
- resolves middle dot component
- resolves trailing dot
- resolves multiple consecutive dots
- resolves dot after absolute path
- resolves trailing parent ref
- resolves middle parent ref
- resolves multiple parent refs
- resolves parent at root — stays at root
- resolves complex mixed dot and dotdot
- handles going above relative root with dotdot
- handles double dotdot above relative root
- collapses double slash in middle
- collapses triple slash
- collapses double slash at start of absolute path
- collapses double slash with dots
- strips trailing slash
- strips multiple trailing slashes
- strips trailing slash on absolute path
- returns dot for empty string
- handles single component
- handles dot-dot only
- handles deeply nested dotdot collapse
- reproduces: dot-slash prefix ./subdir
- reproduces: middle dotdot dir/subdir/../other
- reproduces: double slash from string concat
- reproduces: complex mixed path
- matches lowercase .cmm
- matches uppercase .CMM
- matches mixed case .Cmm
- matches mixed case .cMM
- matches mixed case .CMm
- matches long filename
- matches filename with dots
- matches minimum length name
- rejects .txt extension
- rejects .c extension
- rejects .cmm prefix without dot
- rejects too short name
- rejects partial extension .cm
- rejects .cmmx extension
- rejects empty string
- rejects no extension
- detects name without extension as directory
- detects name without extension — underscore
- detects name without extension — digits
- detects name with very long pseudo-extension
- detects .cmm as file
- detects .txt as file
- detects .c as file
- detects .h as file
- detects .py as file
- detects .cmm uppercase as file
- skips .git directory
- skips .svn directory
- skips .gitignore file
- skips .hidden
- skips dotfile with extension
- handles single char name as directory
- handles name ending with dot only
- finds needle at start
- finds needle in middle
- finds needle at end
- finds exact match
- returns false for missing needle
- returns false when needle longer than haystack
- returns false for empty haystack
- finds empty needle
- handles single char needle
- handles single char miss
- handles repeated pattern
- matches prefix
- matches full string
- matches empty prefix
- rejects wrong prefix
- rejects longer prefix
