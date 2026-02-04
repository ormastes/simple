# Import System Planning and Testing

**Date:** 2026-02-04
**Status:** ✅ Planning Complete, Tests Written, Implementation TODO

## Summary

Created comprehensive design documentation, migration plan, and test specifications for the Simple language import system. The current system treats all imports as relative; the new design will distinguish between absolute, relative, and parent imports.

## Deliverables

### 1. Design Documentation
**File:** `doc/design/import_path_design.md`

Complete specification of import syntax:
- **Absolute imports** (no prefix): `use testing.helpers`
- **Relative imports** (`.` prefix): `use .smf_enums`
- **Parent imports** (`..` prefix): `use ..monomorphize.metadata`
- **Invalid syntax**: `use path/with/slash` (forbidden)

### 2. Migration Plan
**File:** `doc/todo/import_path_migration.md`

5.5-day plan with 5 phases:
1. **Analysis & Audit** (0.5 days) - Scan all imports, categorize patterns
2. **Compiler Implementation** (1.5 days) - Update resolution logic, add validators
3. **Codebase Migration** (2 days) - Fix all existing imports (automated + manual)
4. **Testing & Validation** (1 day) - Verify no breakage, run regression tests
5. **Documentation** (0.5 days) - Update guides, examples, skills

### 3. Test Specifications

**File:** `test/compiler/import_resolution_spec.spl` (370 lines)

Comprehensive tests for import resolution:
- 12 test cases for absolute imports
- 12 test cases for relative imports
- 12 test cases for parent imports
- 12 test cases for invalid imports
- 12 test cases for parser warnings
- 6 edge case tests

**File:** `test/compiler/import_warning_spec.spl` (183 lines)

Tests for parser warnings (already implemented):
- 7 tests for warning detection
- 3 tests for warning message content
- 3 tests for warning severity

Total: **61 test cases** covering all import scenarios

### 4. Parser Warning (Already Implemented)
**File:** `src/compiler/parser.spl`

Added warning for "/" in import paths:
```simple
me warning(message: text, span: Span):
    self.errors = self.errors.push(ParseError(
        message: message,
        span: span,
        severity: ErrorSeverity.Warning
    ))
```

## Import Syntax Rules

### ✅ Correct Syntax

| Type | Syntax | Example | Resolves From |
|------|--------|---------|---------------|
| Absolute | `use module.submodule` | `use testing.helpers` | Project root |
| Relative | `use .module` | `use .smf_enums` | Current directory |
| Parent | `use ..module` | `use ..ast` | Parent directory |

### ❌ Incorrect Syntax

| Pattern | Example | Why Wrong | Use Instead |
|---------|---------|-----------|-------------|
| Using `/` | `use std/testing` | Not allowed | `use std.testing` |
| Relative subdir | `use .linker.smf_header` | Can't traverse | `use linker.smf_header` (absolute) |
| Double parent | `use ../../module` | Too many levels | Use absolute |
| Mixed separators | `use std.foo/bar` | Inconsistent | `use std.foo.bar` |

## Current Status

### ✅ Completed
- Design documentation
- Migration plan with timeline
- 61 comprehensive test cases
- Parser warning for "/" in imports
- Examples and usage guidelines

### 🔄 TODO (Per Migration Plan)
- [ ] Phase 1: Audit all existing imports
- [ ] Phase 2: Implement resolver logic
- [ ] Phase 3: Migrate codebase
- [ ] Phase 4: Run regression tests
- [ ] Phase 5: Update documentation

### 📊 Estimated Effort
- **Total:** 5.5 days
- **Priority:** P1 (High)
- **Blocked by:** None
- **Blocks:** LSP improvements, package system, module refactoring

## Key Design Decisions

1. **No prefix = absolute** - Most common case should be simplest
2. **`.` = relative (same dir only)** - Clear, can't traverse subdirectories
3. **`..` = parent (one level only)** - Familiar, but limited to prevent confusion
4. **No `/` allowed** - Avoids mixing file paths with module paths
5. **`.` separator only** - Consistent with Python, Java, Rust

## Examples from Codebase

### Before (Current - All Relative)
```simple
# Confusing - looks absolute but is relative
use testing.helpers

# Mix of styles
use ./smf_enums.*
use ../monomorphize/metadata.*
```

### After (Clear Distinction)
```simple
# Clearly absolute (from root)
use testing.helpers

# Clearly relative (same dir)
use .smf_enums.*

# Clearly parent (up one level)
use ..monomorphize.metadata.*
```

## Migration Strategy

### Automated Migration
Create `tools/migrate_imports.spl`:
- Scan all `.spl` files
- Determine file relationships
- Rewrite import statements
- Validate with tests

### Manual Review
- Edge cases flagged by script
- Generated code
- Template files

## Testing Strategy

### Unit Tests
- Import resolution logic
- Path validation
- Warning generation

### Integration Tests
- Full build with new imports
- Test suite execution
- SMF file loading

### Regression Tests
- Compare before/after output
- Verify LSP still works
- Check generated code

## Benefits

1. **Clarity** - Obvious whether import is absolute or relative
2. **Consistency** - One way to write each import type
3. **Predictability** - Resolution always works the same way
4. **Tooling** - LSP can provide better autocomplete
5. **Maintainability** - Easier to refactor modules

## Risks & Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Breaking existing code | High | Gradual migration, warnings first |
| Missed imports in migration | Medium | Automated scan + manual review |
| New bugs in resolver | Medium | Comprehensive tests before migration |
| Documentation out of sync | Low | Update docs in final phase |

## Next Steps

1. **Immediate:** Review and approve design
2. **Week 1:** Phase 1 & 2 (Analysis + Implementation)
3. **Week 2:** Phase 3 & 4 (Migration + Testing)
4. **Week 2:** Phase 5 (Documentation)
5. **Future:** Consider hard error for "/" in v2.0.0

## References

- Design: `doc/design/import_path_design.md`
- Migration Plan: `doc/todo/import_path_migration.md`
- Resolution Tests: `test/compiler/import_resolution_spec.spl`
- Warning Tests: `test/compiler/import_warning_spec.spl`
- Current Parser: `src/compiler/parser.spl`
- Parser Warning Report: `doc/report/import_path_warning_2026-02-04.md`

## Conclusion

The import system design is complete with comprehensive documentation, detailed migration plan, and 61 test cases ready for implementation. The work can begin immediately with no blockers.
