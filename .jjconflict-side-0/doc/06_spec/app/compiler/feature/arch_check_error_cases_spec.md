# Architecture Check Error Cases

**Feature ID:** #ARCH-001 | **Category:** Tooling | **Status:** Active

_Source: `test/feature/usage/arch_check_error_cases_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 43 |

## Test Structure

### Arch Check Error Cases: _str_trim edge cases

- ✅ handles already-trimmed string unchanged
- ✅ handles empty string
- ✅ handles string of only spaces
- ✅ handles string of only tabs
- ✅ handles single character
- ✅ handles string with tab and spaces
### Arch Check Error Cases: _parse_pattern_list edge cases

- ✅ returns empty list for empty brackets
- ✅ returns empty list for missing brackets
- ✅ returns empty list for empty input string
- ✅ parses single quoted pattern
- ✅ parses single item with double quotes
- ✅ ignores whitespace around patterns
### Arch Check Error Cases: _match_pattern edge cases

- ✅ empty pattern does not match non-empty import
- ✅ empty import does not match non-empty pattern
- ✅ empty import matches empty pattern exactly
- ✅ /** suffix matches any subpath of prefix
- ✅ pattern exact does not match import with extra segment
- ✅ /* does not match two levels deep
- ✅ /* matches single level sub-path
- ✅ prefix match requires slash boundary
- ✅ exact match succeeds for identical strings
- ✅ pattern with /** matches direct child
### Arch Check Error Cases: _is_import_allowed edge cases

- ✅ import allowed when both allow and deny lists are empty
- ✅ import denied when not in non-empty allow list
- ✅ import allowed when in allow list and deny list is empty
- ✅ import denied when matched by deny pattern even if in allow list
- ✅ import allowed when in allow but not in deny
### Arch Check Error Cases: _parse_imports_from_content edge cases

- ✅ returns empty list for empty content
- ✅ returns empty list for content with no use statements
- ✅ ignores comment lines starting with #
- ✅ strips trailing dot from module path
- ✅ converts dot notation to slash notation
### Arch Check Error Cases: _module_path_from_init_file edge cases

- ✅ returns __init__.spl when init file is directly under root with no subdir
- ✅ handles path not under root unchanged
### Arch Check Error Cases: _file_is_under_module edge cases

- ✅ empty module path matches any file
- ✅ file at exact module boundary matches
- ✅ file outside module boundary does not match
- ✅ file with similar prefix but different module does not match
### Arch Check Error Cases: _parse_arch_block edge cases

- ✅ returns false for empty content
- ✅ returns true when arch keyword appears in comment because parser has no comment awareness
- ✅ returns empty allow and deny for arch block with no imports section
- ✅ parses arch block with empty allow list
- ✅ parses arch block with empty deny list

