# Phase 2: Shared Library Extraction Plan

**Date:** 2026-02-14
**Purpose:** Actionable roadmap for consolidating cross-module duplications
**Status:** Proposal - Pending review

---

## Overview

This document provides step-by-step implementation plans for the 7 major duplication patterns identified in Phase 2 analysis. Each section includes:
- Target file structure
- Migration checklist
- Breaking change analysis
- Test requirements

---

## 1. Backend Types Unification

### Target Architecture

```
src/compiler_core/backend_types.spl          # Canonical definitions (158 lines, KEEP)
src/compiler/backend/backend_types.spl  # DELETE (400 lines)
src/compiler/backend/backend_extensions.spl  # NEW (optional helper functions)
```

### Step-by-Step Migration

**Phase 1: Preparation (30 min)**
1. Inventory all imports of `compiler.backend.backend_types`
   ```bash
   grep -r "use.*compiler\.backend\.backend_types" src/
   ```
2. Create backup branch
   ```bash
   jj new -m "wip: backend types unification"
   ```

**Phase 2: Extract Extensions (1 hour)**
1. Identify impl block methods in `src/compiler/backend/backend_types.spl`
2. Convert to free functions in `src/compiler/backend/backend_extensions.spl`:
   ```simple
   # Before (impl block)
   impl BackendKind:
       fn supports_target(target: CodegenTarget) -> bool:
           match self:
               case Cranelift: target.is_64bit()
               case Llvm: true
               # ...

   # After (free function)
   fn backend_supports_target(backend: BackendKind, target: CodegenTarget) -> bool:
       match backend:
           case BackendKind.Cranelift: target_is_64bit(target)
           case BackendKind.Llvm: true
           # ...
   ```

**Phase 3: Update Imports (30 min)**
1. Replace all compiler backend imports:
   ```simple
   # Before
   use compiler.backend.backend_types.{BackendKind, CodegenTarget}

   # After
   use core.backend_types.{BackendKind, CodegenTarget}
   use compiler.backend.backend_extensions.{backend_supports_target}
   ```

**Phase 4: Delete Old File (5 min)**
1. Remove `src/compiler/backend/backend_types.spl`
2. Update `src/compiler/backend/mod.spl` exports

**Phase 5: Test (30 min)**
1. Run full test suite:
   ```bash
   bin/simple test
   ```
2. Specifically test backend selection:
   ```bash
   bin/simple test test/unit/compiler/backend/
   ```

### Breaking Changes

**None** - All enum variants remain identical

### Success Criteria

- [ ] All tests pass
- [ ] Zero import errors
- [ ] 400 lines removed
- [ ] No runtime regressions

---

## 2. Unified Configuration Parser

### Target Architecture

```
src/lib/config_parser.spl           # NEW (200-250 lines)
  - parse_sdn_config()
  - strip_quotes()
  - get_config_field/int/bool/float()
  - ConfigSection struct

src/app/duplicate_check/config.spl  # REFACTOR (106 → 40 lines)
src/app/test_runner_new/sdoctest/config.spl  # REFACTOR (60 → 25 lines)
src/app/build/config.spl            # REFACTOR (100 → 45 lines)
# ... 4 more files ...
```

### Implementation

**Phase 1: Create Base Parser (2-3 hours)**

File: `src/lib/config_parser.spl`

```simple
# Core types
struct ConfigSection:
    """Represents a section in SDN config file."""
    name: text
    fields: {text: text}

struct ConfigParseResult:
    """Result of parsing config file."""
    sections: [ConfigSection]
    errors: [text]

# Main parser
fn parse_sdn_config(content: text) -> ConfigParseResult:
    """Parse Simple Data Notation config format.

    Format:
        section-name:
            key1: value1
            key2: "quoted value"
            nested-key: 123

    Returns:
        ConfigParseResult with sections and any parse errors
    """
    var sections = []
    var errors = []
    var current_section = nil
    var line_num = 0

    for line in content.split(NL):
        line_num = line_num + 1
        val trimmed = line.trim()

        # Skip empty lines and comments
        if trimmed.len() == 0 or trimmed.starts_with("#"):
            continue

        # Section header: "name:" with no spaces before colon
        if trimmed.ends_with(":") and not trimmed.contains(" "):
            if current_section.?:
                sections.push(current_section)
            current_section = ConfigSection(
                name: trimmed[0:-1],
                fields: {}
            )
            continue

        # Key-value pair
        if trimmed.contains(":"):
            if not current_section.?:
                errors.push("Line {line_num}: key-value outside section")
                continue

            val colon_idx = trimmed.index_of(":")
            if colon_idx == nil:
                continue

            val key = trimmed[0:colon_idx].trim()
            val value = trimmed[colon_idx + 1:].trim()

            current_section.fields[key] = strip_quotes(value)
        else:
            # Indented value continuation (future enhancement)
            errors.push("Line {line_num}: unrecognized format")

    # Add final section
    if current_section.?:
        sections.push(current_section)

    ConfigParseResult(sections: sections, errors: errors)

# Utility functions
fn strip_quotes(s: text) -> text:
    """Remove leading/trailing quotes from value."""
    var result = s
    if result.len() >= 2:
        val first = result[0]
        val last = result[-1]
        if (first == "\"" and last == "\"") or (first == "'" and last == "'"):
            result = result[1:-1]
    result

fn find_section(result: ConfigParseResult, name: text) -> ConfigSection?:
    """Find section by name."""
    for section in result.sections:
        if section.name == name:
            return section
    nil

# Type-safe getters
fn get_config_field(section: ConfigSection, key: text, default_val: text) -> text:
    """Get string field with default."""
    if section.fields.contains_key(key):
        section.fields[key]
    else:
        default_val

fn get_config_int(section: ConfigSection, key: text, default_val: i64) -> i64:
    """Get integer field with default."""
    val str_val = get_config_field(section, key, "")
    if str_val.len() > 0:
        int(str_val)
    else:
        default_val

fn get_config_bool(section: ConfigSection, key: text, default_val: bool) -> bool:
    """Get boolean field with default."""
    val str_val = get_config_field(section, key, "")
    if str_val == "true":
        true
    elif str_val == "false":
        false
    else:
        default_val

fn get_config_float(section: ConfigSection, key: text, default_val: f64) -> f64:
    """Get float field with default."""
    val str_val = get_config_field(section, key, "")
    if str_val.len() > 0:
        float(str_val)
    else:
        default_val

fn get_config_list(section: ConfigSection, key: text, separator: text) -> [text]:
    """Get comma-separated list field."""
    val str_val = get_config_field(section, key, "")
    if str_val.len() == 0:
        return []
    str_val.split(separator)

# Export all
export ConfigSection, ConfigParseResult
export parse_sdn_config, strip_quotes, find_section
export get_config_field, get_config_int, get_config_bool, get_config_float, get_config_list
```

**Phase 2: Add Tests (1 hour)**

File: `test/unit/std/config_parser_spec.spl`

```simple
use std.spec.{describe, it, expect}
use std.config_parser.{parse_sdn_config, find_section, get_config_int, get_config_bool}

fn test():
    describe "config_parser":
        it "parses simple section":
            val content = "database:\n  host: localhost\n  port: 5432"
            val result = parse_sdn_config(content)

            expect(result.sections.len()).to_equal(1)
            val section = result.sections[0]
            expect(section.name).to_equal("database")
            expect(section.fields["host"]).to_equal("localhost")
            expect(section.fields["port"]).to_equal("5432")

        it "strips quotes from values":
            val content = "app:\n  name: \"My App\"\n  version: '1.0'"
            val result = parse_sdn_config(content)
            val section = result.sections[0]

            expect(section.fields["name"]).to_equal("My App")
            expect(section.fields["version"]).to_equal("1.0")

        it "handles multiple sections":
            val content = "section1:\n  key1: val1\nsection2:\n  key2: val2"
            val result = parse_sdn_config(content)

            expect(result.sections.len()).to_equal(2)
            expect(result.sections[0].name).to_equal("section1")
            expect(result.sections[1].name).to_equal("section2")

        it "type-safe getters with defaults":
            val content = "config:\n  count: 42\n  enabled: true"
            val result = parse_sdn_config(content)
            val section = result.sections[0]

            expect(get_config_int(section, "count", 0)).to_equal(42)
            expect(get_config_bool(section, "enabled", false)).to_equal(true)
            expect(get_config_int(section, "missing", 99)).to_equal(99)

        it "reports errors for malformed input":
            val content = "key: value"  # No section
            val result = parse_sdn_config(content)

            expect(result.errors.len()).to_be_greater_than(0)
```

**Phase 3: Migrate Duplicate Check (1 hour)**

Before (`src/app/duplicate_check/config.spl`): 106 lines

After:
```simple
use std.config_parser.{parse_sdn_config, find_section, get_config_int, get_config_bool, get_config_list}
use app.io.mod.{file_exists, file_read}

# Keep struct definition
struct DuplicationConfig:
    min_tokens: i64
    min_lines: i64
    # ... 20 fields ...

fn default_config() -> DuplicationConfig:
    # Same as before
    ...

fn parse_config_file(content: text) -> DuplicationConfig:
    val result = parse_sdn_config(content)
    val section = find_section(result, "duplicate-check")

    if not section.?:
        return default_config()

    var config = default_config()

    config.min_tokens = get_config_int(section, "min-tokens", config.min_tokens)
    config.min_lines = get_config_int(section, "min-lines", config.min_lines)
    config.min_impact = get_config_int(section, "min-impact", config.min_impact)
    config.ignore_identifiers = get_config_bool(section, "ignore-identifiers", config.ignore_identifiers)
    config.use_cosine_similarity = get_config_bool(section, "use-cosine-similarity", config.use_cosine_similarity)
    config.exclude_patterns = get_config_list(section, "exclude", ",")

    config

fn load_config() -> DuplicationConfig:
    # Same as before
    ...
```

**Lines reduced:** 106 → ~50 (56 lines saved)

**Phase 4: Migrate Other Configs (3-4 hours)**

Apply same pattern to:
1. `src/app/test_runner_new/sdoctest/config.spl` (60 → 30 lines, save 30)
2. `src/app/build/config.spl` (100 → 50 lines, save 50)
3. `src/app/test/cpu_aware_test.spl` (40 → 20 lines, save 20)
4. `src/app/mcp/fileio_protection.spl` (80 → 40 lines, save 40)

**Total savings:** 200-250 lines base parser + 200 lines migrations = **400-450 net savings**

### Breaking Changes

**None** - All existing APIs remain, internal implementation changes only

### Success Criteria

- [ ] Base parser passes 20+ tests
- [ ] All migrated configs load successfully
- [ ] Existing tool behavior unchanged
- [ ] 400+ lines net reduction

---

## 3. String Utilities Consolidation

### Target Architecture

```
src/lib/string_core.spl             # NEW (150-200 lines, canonical implementations)
src/lib/text.spl                  # KEEP (existing, imports from string_core)
src/lib/template/utilities.spl     # REFACTOR (remove duplicates)
src/compiler_core/types.spl                  # REFACTOR (delegate to string_core)
```

### Implementation

**Phase 1: Create String Core (2 hours)**

File: `src/lib/string_core.spl`

```simple
# ============================================================================
# String Core Utilities
# Canonical implementations - delegates to runtime built-ins when available
# ============================================================================

# Basic operations (delegate to built-ins)
fn str_len(s: text) -> i64:
    """Get string length."""
    s.len()

fn str_concat(a: text, b: text) -> text:
    """Concatenate two strings."""
    a + b

fn str_eq(a: text, b: text) -> bool:
    """Check string equality."""
    a == b

# Slicing and access
fn str_slice(s: text, start: i64, end_idx: i64) -> text:
    """Extract substring [start, end)."""
    s[start:end_idx]

fn str_char_at(s: text, idx: i64) -> text:
    """Get character at index."""
    if idx < 0 or idx >= s.len():
        return ""
    s[idx]

# Search operations
fn str_contains(s: text, needle: text) -> bool:
    """Check if string contains substring."""
    s.contains(needle)

fn str_starts_with(s: text, prefix: text) -> bool:
    """Check if string starts with prefix."""
    s.starts_with(prefix)

fn str_ends_with(s: text, suffix: text) -> bool:
    """Check if string ends with suffix."""
    s.ends_with(suffix)

fn str_index_of(s: text, needle: text) -> i64:
    """Find first occurrence of substring. Returns -1 if not found."""
    val result = s.index_of(needle)
    if result == nil:
        -1
    else:
        result

fn str_last_index_of(s: text, needle: text) -> i64:
    """Find last occurrence of substring. Returns -1 if not found."""
    var last_pos = -1
    var search_start = 0

    while search_start < s.len():
        val pos = str_index_of(s[search_start:], needle)
        if pos == -1:
            break
        last_pos = search_start + pos
        search_start = last_pos + 1

    last_pos

# Transformation
fn str_trim(s: text) -> text:
    """Remove leading and trailing whitespace."""
    s.trim()

fn str_trim_left(s: text) -> text:
    """Remove leading whitespace."""
    var i = 0
    while i < s.len():
        val ch = s[i]
        if ch != " " and ch != "\t" and ch != "\n" and ch != "\r":
            break
        i = i + 1
    s[i:]

fn str_trim_right(s: text) -> text:
    """Remove trailing whitespace."""
    var i = s.len() - 1
    while i >= 0:
        val ch = s[i]
        if ch != " " and ch != "\t" and ch != "\n" and ch != "\r":
            break
        i = i - 1
    s[0:i + 1]

fn str_replace(s: text, old_val: text, new_val: text) -> text:
    """Replace first occurrence of old with new."""
    s.replace(old_val, new_val)

fn str_replace_all(s: text, old_val: text, new_val: text) -> text:
    """Replace all occurrences of old with new."""
    var result = s
    while result.contains(old_val):
        result = result.replace(old_val, new_val)
    result

# Splitting and joining
fn str_split(s: text, delimiter: text) -> [text]:
    """Split string by delimiter."""
    s.split(delimiter)

fn str_join(parts: [text], separator: text) -> text:
    """Join strings with separator."""
    parts.join(separator)

# Case conversion (requires char mapping)
fn str_to_lower(s: text) -> text:
    """Convert to lowercase."""
    # TODO: Check if runtime has built-in, else implement char mapping
    var result = ""
    var i = 0
    while i < s.len():
        val ch = s[i]
        if ch >= "A" and ch <= "Z":
            val code = char_code(ch)
            result = result + char_from_code(code + 32)
        else:
            result = result + ch
        i = i + 1
    result

fn str_to_upper(s: text) -> text:
    """Convert to uppercase."""
    var result = ""
    var i = 0
    while i < s.len():
        val ch = s[i]
        if ch >= "a" and ch <= "z":
            val code = char_code(ch)
            result = result + char_from_code(code - 32)
        else:
            result = result + ch
        i = i + 1
    result

# Helper for case conversion (depends on std.text.char_code)
use std.text.{char_code}

fn char_from_code(code: i64) -> text:
    """Convert ASCII code to character."""
    # Implementation depends on runtime capabilities
    # For now, use lookup table approach
    if code == 65: return "A"
    if code == 66: return "B"
    # ... (full implementation needed)
    "?"

export str_len, str_concat, str_eq
export str_slice, str_char_at
export str_contains, str_starts_with, str_ends_with
export str_index_of, str_last_index_of
export str_trim, str_trim_left, str_trim_right
export str_replace, str_replace_all
export str_split, str_join
export str_to_lower, str_to_upper
```

**Phase 2: Update Core Types (15 min)**

File: `src/compiler_core/types.spl`

```simple
# Before: 35 lines of implementations

# After: 3 lines
use std.text_core.{str_concat, str_len, str_eq, str_slice, str_char_at, str_contains, str_starts_with, str_ends_with, str_index_of, str_trim, str_replace}

# Re-export for backwards compatibility
export str_concat, str_len, str_eq, str_slice, str_char_at, str_contains, str_starts_with, str_ends_with, str_index_of, str_trim, str_replace
```

**Phase 3: Cleanup Template Utilities (30 min)**

File: `src/lib/template/utilities.spl`

Remove functions now in string_core:
- Lines 40-180 (str_* functions)

Keep template-specific utilities:
- Template variable substitution
- Escaping helpers
- Template-specific transformations

**Estimated savings:** 100-120 lines

### Breaking Changes

**None** - All existing imports continue to work via re-exports

### Success Criteria

- [ ] All string tests pass
- [ ] Template engine works unchanged
- [ ] Core types compiles
- [ ] 250-300 lines saved

---

## 4. Error Handling Consolidation

### Target Architecture

```
src/lib/error_core.spl              # NEW (base trait, formatting)
src/lib/error_format.spl            # NEW (formatting utilities)
src/compiler_core/error.spl                  # REFACTOR (uses error_core)
src/lib/error.spl                   # REFACTOR (implements error_core)
src/compiler/backend/codegen_errors.spl  # REFACTOR (implements error_core)
```

### Implementation Plan

**Phase 1: Create Error Core (1-2 hours)**

See detailed example in main report section 3.

**Phase 2: Migrate Core Errors (1 hour)**
**Phase 3: Migrate Std Errors (1 hour)**
**Phase 4: Migrate Codegen Errors (1 hour)**

### Success Criteria

- [ ] All error types implement ErrorBase
- [ ] Consistent formatting across modules
- [ ] 150-200 lines saved
- [ ] Zero test failures

---

## 5-7. Lower Priority Items

See main report for:
- Integer conversion investigation
- Loop pattern documentation
- Semantic types registry

---

## Implementation Timeline

### Week 1: Foundation (8-10 hours)
- Day 1-2: Backend types unification (Priority 1, 2-3 hours)
- Day 3-5: Config parser creation + migration (Priority 1, 6-7 hours)

### Week 2: String & Error (6-8 hours)
- Day 1-2: String utilities consolidation (Priority 1, 3-4 hours)
- Day 3-4: Error handling consolidation (Priority 2, 3-4 hours)

### Week 3: Cleanup & Documentation (4-6 hours)
- Day 1: Integer conversion investigation (Priority 2, 2 hours)
- Day 2: Documentation updates (Priority 3, 2-3 hours)
- Day 3: Review and testing (1 hour)

**Total estimated effort:** 18-24 hours over 3 weeks

---

## Risk Mitigation

### Before Each Migration

1. **Create feature branch:**
   ```bash
   jj new -m "refactor: [item name]"
   ```

2. **Run baseline tests:**
   ```bash
   bin/simple test > baseline_results.txt
   ```

3. **Document current behavior:**
   - Note any quirks or edge cases
   - Identify breaking change risks

### After Each Migration

1. **Run full test suite:**
   ```bash
   bin/simple test
   diff baseline_results.txt current_results.txt
   ```

2. **Smoke test key tools:**
   ```bash
   bin/simple build
   bin/simple duplicate-check src/core
   bin/simple test test/unit/std/
   ```

3. **Review imports:**
   ```bash
   grep -r "use.*[old_module]" src/ test/
   ```

### Rollback Plan

If issues arise:
```bash
jj abandon  # Discard current change
jj restore @-  # Return to previous state
```

---

## Metrics Tracking

### Before Refactoring

```bash
# Line counts
wc -l src/compiler_core/backend_types.spl  # 158
wc -l src/compiler/backend/backend_types.spl  # 400+
wc -l src/app/*/config.spl  # ~600
wc -l src/lib/text.spl src/lib/template/utilities.spl  # 500+

# Test coverage
bin/simple test --coverage
```

### After Refactoring

```bash
# Expected reductions
# backend_types: -400
# config parsers: -400
# string utilities: -250
# error handling: -150
# Total: -1,200 lines

bin/simple test --coverage  # Should maintain or improve coverage
```

---

## Conclusion

This plan provides a structured, low-risk approach to eliminating 1,200+ lines of duplicated code while maintaining 100% backwards compatibility and test coverage. Each phase is independently testable and reversible.

**Next action:** Review this plan with team, prioritize items, and schedule implementation sprints.

---

**End of Plan**
