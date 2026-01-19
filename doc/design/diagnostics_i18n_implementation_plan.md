# Diagnostics I18n Implementation Plan

**Date**: 2026-01-19
**Status**: Planning Phase
**Goal**: Complete integration of i18n system with all diagnostic messages

---

## Executive Summary

This document provides a comprehensive plan to integrate the i18n system with all diagnostic messages in the Simple compiler. The i18n infrastructure is **complete** (Phases 1-4 done), and catalog files exist with Korean translations. The remaining work is to **convert Rust code** from hardcoded error strings to use the i18n diagnostic system.

---

## Current Status

### ✅ What's Complete

**Infrastructure (100%)**:
- ✅ Core i18n crate (`src/i18n/`) - 800+ LOC, 21 tests passing
- ✅ Build-time catalog compilation with phf maps
- ✅ Runtime locale loading with fallback chain (ko_KR → ko → en)
- ✅ CLI `--lang` flag integration in driver
- ✅ Diagnostic formatters (Text, JSON, Simple)
- ✅ Conversion helpers (`convert_parser_diagnostic()`)

**Parser Errors (100%)**:
- ✅ E0001-E0012 defined in `i18n/parser.spl`
- ✅ E0001-E0012 translated in `i18n/parser.ko.spl`
- ✅ Conversion helper in `src/driver/src/diagnostics_conversion.rs`

**Compiler Errors (50% - Catalogs Only)**:
- ✅ E1001-E3005 defined in `i18n/compiler.spl` (24 error codes)
- ✅ E1001-E3005 translated in `i18n/compiler.ko.spl`
- ❌ Rust code NOT yet using these catalogs

### 🚧 What's Missing

**Compiler Integration (0%)**:
- ❌ Rust error messages still use `format!()` with hardcoded strings
- ❌ No `error_i18n()` calls in compiler code
- ❌ Runtime errors not in catalogs
- ❌ FFI errors not cataloged
- ❌ Panic messages not cataloged

---

## Diagnostic Message Inventory

### 1. Parser Errors (E0xxx) - ✅ COMPLETE

| Code | Title | Location | i18n Status |
|------|-------|----------|-------------|
| E0001 | Syntax Error | `parser/error.rs:54-71` | ✅ Complete |
| E0002 | Unexpected Token | `parser/error.rs:73-79` | ✅ Complete |
| E0003 | Unexpected EOF | `parser/error.rs:103-172` | ✅ Complete |
| E0004 | Invalid Integer Literal | `parser/error.rs:103-172` | ✅ Complete |
| E0005 | Invalid Float Literal | `parser/error.rs:103-172` | ✅ Complete |
| E0006 | Invalid Escape Sequence | `parser/error.rs:103-172` | ✅ Complete |
| E0007 | Unclosed String Literal | `parser/error.rs:103-172` | ✅ Complete |
| E0008 | Invalid Indentation | `parser/error.rs:103-172` | ✅ Complete |
| E0009 | Unterminated Block Comment | `parser/error.rs:103-172` | ✅ Complete |
| E0010 | Missing Expected Token | `parser/error.rs:103-172` | ✅ Complete |
| E0011 | Invalid Pattern | `parser/error.rs:103-172` | ✅ Complete |
| E0012 | Invalid Type | `parser/error.rs:103-172` | ✅ Complete |

**Status**: Parser errors use `to_diagnostic()` which creates English messages, then `convert_parser_diagnostic()` in driver converts to i18n. This works but is indirect.

### 2. Compiler Semantic Errors (E10xx) - 📦 Cataloged, ❌ Not Integrated

| Code | Title | Catalog | Korean | Rust Code |
|------|-------|---------|--------|-----------|
| E1001 | Undefined Variable | ✅ | ✅ | ❌ Uses `format!()` |
| E1002 | Undefined Function | ✅ | ✅ | ❌ Uses `format!()` |
| E1003 | Type Mismatch | ✅ | ✅ | ❌ Uses `format!()` |
| E1004 | Invalid Assignment | ✅ | ✅ | ❌ Uses `format!()` |
| E1005 | Invalid Operation | ✅ | ✅ | ❌ Uses `format!()` |
| E1006 | Invalid Pattern | ✅ | ✅ | ❌ Uses `format!()` |
| E1007 | Missing Field | ✅ | ✅ | ❌ Uses `format!()` |
| E1008 | Duplicate Definition | ✅ | ✅ | ❌ Uses `format!()` |
| E1009 | Circular Dependency | ✅ | ✅ | ❌ Uses `format!()` |
| E1010 | Module Not Found | ✅ | ✅ | ❌ Uses `format!()` |

**Locations**:
- `compiler/error.rs:295-493` - CompileError enum
- `compiler/interpreter.rs:261-849` - Semantic errors with `format!()`

### 3. Control Flow Errors (E11xx) - 📦 Cataloged, ❌ Not Integrated

| Code | Title | Catalog | Korean | Rust Code |
|------|-------|---------|--------|-----------|
| E1101 | Break Outside Loop | ✅ | ✅ | ❌ Not found in code |
| E1102 | Continue Outside Loop | ✅ | ✅ | ❌ Not found in code |
| E1103 | Return Outside Function | ✅ | ✅ | ❌ Not found in code |

**Note**: These errors may be in semantic analysis phase, need to verify.

### 4. Macro Errors (E14xx) - 📦 Cataloged, ❌ Not Integrated

| Code | Title | Catalog | Korean | Rust Code |
|------|-------|---------|--------|-----------|
| E1401 | Undefined Macro | ✅ | ✅ | ❌ Not found in code |
| E1402 | Macro Used Before Definition | ✅ | ✅ | ❌ Not found in code |

### 5. Codegen Errors (E20xx) - 📦 Cataloged, ❌ Not Integrated

| Code | Title | Catalog | Korean | Rust Code |
|------|-------|---------|--------|-----------|
| E2001 | Unsupported Feature | ✅ | ✅ | ❌ Uses `CompileError::Semantic()` |
| E2002 | FFI Error | ✅ | ✅ | ❌ Uses string format |

**Locations**:
- `compiler/codegen/llvm/functions/*.rs` - Multiple files
- Error messages: "Failed to build load", "Failed to build store", etc.

### 6. Runtime Errors (E30xx) - 📦 Cataloged, ❌ Not Integrated

| Code | Title | Catalog | Korean | Rust Code |
|------|-------|---------|--------|-----------|
| E3001 | Division by Zero | ✅ | ✅ | ❌ Uses panic |
| E3002 | Index Out of Bounds | ✅ | ✅ | ❌ Uses panic |
| E3003 | Stack Overflow | ✅ | ✅ | ❌ Uses panic |
| E3004 | Assertion Failed | ✅ | ✅ | ❌ Uses panic |
| E3005 | Timeout | ✅ | ✅ | ❌ Not found in code |

**Locations**:
- `runtime/value/ffi/error_handling.rs:35-84` - Function/method not found
- `runtime/value/ffi/contracts.rs:52-122` - Contract violations
- `runtime/value/ffi/file_io/*.rs` - File I/O panics

### 7. Uncataloged Error Messages

**Interpreter Errors** (`compiler/interpreter.rs`):
- "await failed: {}" (line 130)
- "Promise rejected: {:?}" (line 150)
- "let binding '{}': {}" (lines 261, 271)
- "cannot assign to const '{}'" (line 313)
- Many more semantic errors (lines 320-849)

**Runtime FFI Errors** (`runtime/value/ffi/error_handling.rs`):
- "Runtime error: Function not found (unknown name)"
- "Runtime error: Function '{}' not found"
- "Runtime error: Method '{}' not found on type '{}'"

**Codegen Errors** (`compiler/codegen/llvm/functions/*.rs`):
- "Failed to build load"
- "Failed to build store"
- "Failed to build alloca"
- "Failed to build call"
- "Failed to cast float to int"
- "Unsupported return type"
- Many more (50+ unique messages)

**HIR Lowering Errors** (`compiler/hir/lower/error.rs`):
- E0x series (Unknown type, variable, type mismatch)
- CTR-032, CTR-060-062 (Contract errors)
- Capability errors
- Module resolution errors

**Panic Messages** (Various files):
- AOP: "around advice did not call proceed() exactly once"
- Vulkan: "Expected Resized event", etc.
- File I/O: "mmap failed", "munmap failed"
- Contracts: "{} violation in function '{}': contract condition failed"

---

## Implementation Plan

### Phase 1: Extend Compiler Catalogs (2-3 hours)

**Goal**: Add all missing error messages to `i18n/compiler.spl` and translate to Korean.

**Tasks**:

1. **Audit Uncataloged Messages**
   - Extract all `format!()` error messages from Rust code
   - Assign error codes (continue E-series numbering)
   - Document context parameters for each message

2. **Extend English Catalog** (`i18n/compiler.spl`)
   - Add E11xx series (remaining control flow errors)
   - Add E12xx series (actor/concurrency errors if any)
   - Add E13xx series (memory errors if any)
   - Add E14xx series (remaining macro errors)
   - Add E15xx series (HIR lowering errors)
   - Add E20xx series (remaining codegen errors)
   - Add E30xx series (remaining runtime errors)
   - Add E40xx series (FFI errors)
   - Add E50xx series (panic/invariant violations)

3. **Create Korean Translations** (`i18n/compiler.ko.spl`)
   - Translate all new entries
   - Follow existing terminology conventions
   - Use formal polite form (합니다체)
   - Handle Korean particles properly (e.g., "이(가)", "을(를)")

**Estimated new error codes**: 50-100 (depending on granularity)

**Deliverables**:
- [ ] Extended `i18n/compiler.spl` (+50-100 entries)
- [ ] Extended `i18n/compiler.ko.spl` (+50-100 entries)
- [ ] Error code mapping document

### Phase 2: Integrate Compiler Errors (3-4 hours)

**Goal**: Convert compiler code to use `Diagnostic::error_i18n()`.

**Approach**:

**Before** (current):
```rust
// compiler/interpreter.rs
return Err(CompileError::Semantic(format!(
    "let binding '{}': {}",
    name,
    err
)));
```

**After** (i18n):
```rust
use simple_diagnostics::{Diagnostic, i18n::ctx2};

let ctx = ctx2("name", name, "error", err);
return Err(CompileError::from_diagnostic(
    Diagnostic::error_i18n("compiler", "E1015", &ctx)
        .with_span(span)
        .with_label(span, "binding failed here")
));
```

**Tasks**:

1. **Update `CompileError` Enum**
   - Add `Diagnostic(Diagnostic)` variant
   - Add `from_diagnostic()` constructor
   - Update `to_diagnostic()` to handle new variant

2. **Convert Semantic Errors** (`compiler/interpreter.rs`)
   - Replace ~50 `format!()` calls with `error_i18n()`
   - Extract context parameters
   - Add span information where available

3. **Convert HIR Lowering Errors** (`compiler/hir/lower/error.rs`)
   - Map existing error variants to catalog IDs
   - Add context extraction
   - Update error creation sites

4. **Convert Codegen Errors** (`compiler/codegen/llvm/functions/*.rs`)
   - Replace "Failed to build X" messages
   - Add technical details in context
   - Preserve LLVM error information

**Files to Modify**:
- `src/compiler/Cargo.toml` - Add `simple-diagnostics` dependency
- `src/compiler/src/error.rs` - Add Diagnostic variant
- `src/compiler/src/interpreter.rs` - Convert ~50 error sites
- `src/compiler/src/hir/lower/error.rs` - Convert error enum
- `src/compiler/src/codegen/llvm/functions/*.rs` - Convert 5 files

**Deliverables**:
- [ ] Compiler uses `simple-diagnostics`
- [ ] All semantic errors use i18n
- [ ] All codegen errors use i18n
- [ ] Tests updated and passing

### Phase 3: Integrate Runtime Errors (2-3 hours)

**Goal**: Convert runtime FFI errors to use i18n diagnostics.

**Challenges**:
- Runtime is separate from compiler
- Needs to output errors at runtime, not compile-time
- May need different approach (e.g., format strings in runtime)

**Options**:

**Option A**: Embed i18n in runtime
- Add `simple_i18n` dependency to runtime crate
- Use `I18n::global()` for runtime error messages
- Pro: Consistent with compiler
- Con: Increases runtime binary size

**Option B**: Pre-format error strings at compile-time
- Compiler embeds localized error strings
- Runtime receives pre-formatted messages
- Pro: Zero runtime overhead
- Con: Less flexible, harder to maintain

**Recommendation**: Option A for consistency

**Tasks**:

1. **Add i18n to Runtime**
   - Add `simple_i18n` dependency to `runtime/Cargo.toml`
   - Create runtime error catalog (`i18n/runtime.spl`)
   - Translate to Korean (`i18n/runtime.ko.spl`)

2. **Convert FFI Errors** (`runtime/value/ffi/error_handling.rs`)
   - Replace `eprintln!()` with i18n messages
   - Use consistent error format
   - Add error recovery where possible

3. **Convert Contract Errors** (`runtime/value/ffi/contracts.rs`)
   - Replace panic messages with i18n
   - Keep panic behavior (but localized)

4. **Convert File I/O Errors** (`runtime/value/ffi/file_io/*.rs`)
   - Replace assertion messages
   - Add proper error handling (not just panic)

**Files to Modify**:
- `src/runtime/Cargo.toml` - Add dependency
- `src/runtime/src/value/ffi/error_handling.rs`
- `src/runtime/src/value/ffi/contracts.rs`
- `src/runtime/src/value/ffi/file_io/*.rs`
- `i18n/runtime.spl` (new)
- `i18n/runtime.ko.spl` (new)

**Deliverables**:
- [ ] Runtime uses i18n
- [ ] Runtime error catalog created
- [ ] All FFI errors localized
- [ ] Contract violations localized

### Phase 4: Panic Messages (1-2 hours)

**Goal**: Localize panic/invariant violation messages.

**Approach**:

Panic messages are for **internal errors** (bugs), not user errors. These should:
1. Be in English by default (for bug reports)
2. Optionally localized for user-facing panics
3. Include technical details (file, line, context)

**Recommendation**: Keep most panics in English, localize only user-facing panics.

**Tasks**:

1. **Categorize Panics**
   - Internal invariants → Keep in English
   - User-facing errors → Localize

2. **Localize User-Facing Panics**
   - AOP errors (if user-visible)
   - Contract violations (already in Phase 3)
   - Vulkan event errors (if user-visible)

3. **Add Panic Context**
   - File, line, function name
   - Variable values
   - Stack trace info

**Deliverables**:
- [ ] Panic categorization document
- [ ] User-facing panics localized
- [ ] Internal panics enhanced with context

### Phase 5: Testing & Validation (2-3 hours)

**Goal**: Ensure all diagnostics work correctly in both English and Korean.

**Tasks**:

1. **Unit Tests**
   - Test each error code with context
   - Verify interpolation works
   - Check fallback chain

2. **Integration Tests**
   - Create test files that trigger each error
   - Run with `--lang en` and `--lang ko`
   - Verify output matches expected format

3. **Manual Testing**
   - Test common error scenarios
   - Verify formatting (colors, spans, labels)
   - Check Korean grammar/particles

4. **Coverage Report**
   - Document which errors are tested
   - Identify gaps in coverage
   - Create tests for uncovered paths

**Deliverables**:
- [ ] Unit tests for all error codes
- [ ] Integration test suite
- [ ] Manual test checklist
- [ ] Coverage report (>90%)

### Phase 6: Documentation (1-2 hours)

**Goal**: Update documentation for i18n diagnostic system.

**Tasks**:

1. **Error Code Reference** (`doc/reference/error_codes.md`)
   - List all error codes (E0001-E5xxx)
   - Explain each error
   - Provide examples
   - Link to catalog definitions

2. **i18n Developer Guide** (`doc/contributing/i18n_diagnostics.md`)
   - How to add new error codes
   - How to create catalog entries
   - Translation guidelines
   - Testing requirements

3. **User Guide Update** (`doc/guide/i18n.md`)
   - Document `--lang` flag
   - List supported languages
   - Explain fallback behavior
   - Troubleshooting guide

4. **CHANGELOG**
   - Document i18n feature
   - List supported error codes
   - Migration notes

**Deliverables**:
- [ ] Error code reference
- [ ] Developer guide updated
- [ ] User guide updated
- [ ] CHANGELOG entry

---

## Error Code Allocation

### Current Allocation

| Range | Category | Count | Status |
|-------|----------|-------|--------|
| E0001-E0099 | Parser | 12 | ✅ Complete |
| E1001-E1099 | Semantic (Basic) | 10 | 📦 Cataloged |
| E1101-E1199 | Control Flow | 3 | 📦 Cataloged |
| E1201-E1299 | Actor/Concurrency | 0 | ❌ TBD |
| E1301-E1399 | Memory | 0 | ❌ TBD |
| E1401-E1499 | Macros | 2 | 📦 Cataloged |
| E2001-E2099 | Codegen | 2 | 📦 Cataloged |
| E3001-E3099 | Runtime | 5 | 📦 Cataloged |
| E4001-E4099 | FFI | 0 | ❌ TBD |
| E5001-E5099 | Internal/Panic | 0 | ❌ TBD |

### Proposed Extensions

**E15xx: HIR Lowering** (new category)
- E1501: Unknown type in HIR
- E1502: Type inference failed
- E1503: Impure function in contract (CTR-032)
- E1504: Non-snapshot-safe type (CTR-060-062)
- E1505: Capability error
- E1506: Module resolution failed

**E20xx: Codegen** (extend)
- E2003: Failed to build load
- E2004: Failed to build store
- E2005: Failed to build alloca
- E2006: Failed to build call
- E2007: Failed to cast
- E2008: Unsupported return type

**E30xx: Runtime** (extend)
- E3006: Function not found
- E3007: Method not found
- E3008: Invalid argument type
- E3009: Invalid argument count

**E40xx: FFI** (new)
- E4001: External function call failed
- E4002: Invalid FFI signature
- E4003: FFI type mismatch

**E50xx: Internal** (new)
- E5001: AOP invariant violation
- E5002: Memory allocation failed
- E5003: Unexpected state

---

## Migration Strategy

### Gradual Rollout

**Week 1**: Infrastructure
- Phase 1: Extend catalogs
- Ensure all errors have catalog entries

**Week 2**: Compiler Integration
- Phase 2: Convert compiler errors
- Keep old format temporarily for comparison

**Week 3**: Runtime & Testing
- Phase 3: Runtime errors
- Phase 5: Comprehensive testing

**Week 4**: Polish & Documentation
- Phase 4: Panic messages
- Phase 6: Documentation
- Final validation

### Backward Compatibility

**During Migration**:
```rust
#[cfg(feature = "i18n")]
let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx);

#[cfg(not(feature = "i18n"))]
let diag = Diagnostic::error(&format!("cannot find variable `{}`", name));
```

**After Migration**:
- Remove feature flags
- i18n becomes mandatory
- Old `format!()` code removed

---

## Success Criteria

### MVP (Minimum Viable Product)

- [ ] All parser errors use i18n (already done)
- [ ] All compiler semantic errors use i18n
- [ ] All error codes have Korean translations
- [ ] `--lang ko` works end-to-end
- [ ] 90%+ test coverage

### Full Implementation

- [ ] All error messages cataloged (E0001-E5099)
- [ ] All Rust code uses `error_i18n()`
- [ ] Runtime errors localized
- [ ] Panic messages categorized and localized appropriately
- [ ] Comprehensive documentation
- [ ] 95%+ test coverage
- [ ] Native speaker review of Korean translations
- [ ] Integration tests for all error paths

---

## Estimated Timeline

| Phase | Tasks | Estimated Hours |
|-------|-------|-----------------|
| Phase 1 | Extend catalogs | 2-3 hours |
| Phase 2 | Compiler integration | 3-4 hours |
| Phase 3 | Runtime integration | 2-3 hours |
| Phase 4 | Panic messages | 1-2 hours |
| Phase 5 | Testing & validation | 2-3 hours |
| Phase 6 | Documentation | 1-2 hours |
| **Total** | | **11-17 hours** |

**Recommended**: 2-3 days of focused work, or 1 week with other tasks.

---

## Technical Challenges

### Challenge 1: Compiler Circular Dependency

**Problem**: Compiler needs diagnostics, diagnostics need i18n, i18n needs parser

**Solution**: Already solved with layered architecture (see `diagnostics_i18n_complete.md`)

### Challenge 2: Runtime Binary Size

**Problem**: Adding i18n to runtime increases binary size

**Solution**:
- Lazy loading (catalogs loaded on first use)
- Optional feature flag for embedded systems
- Default locale compiled in (zero cost)

### Challenge 3: Panic vs Error

**Problem**: Panic messages are for bugs, not user errors

**Solution**:
- Keep internal panics in English
- Localize user-facing errors
- Clear categorization

### Challenge 4: Context Extraction

**Problem**: Existing errors use format strings, need to extract parameters

**Solution**:
- Systematic regex search for `format!()` calls
- Manual review of each error site
- Create helper functions for common patterns

### Challenge 5: Korean Particles

**Problem**: Korean particles change based on final consonant

**Solution** (current):
- Show both forms: "이(가)", "을(를)"
- Future: Dynamic selection based on placeholder value

---

## Resources

### Documentation References

- **Architecture**: `src/diagnostics/ARCHITECTURE.md`
- **Usage Guide**: `src/diagnostics/USAGE.md`
- **Implementation Status**: `doc/design/diagnostics_i18n_complete.md`
- **i18n Spec**: `doc/design/i18n_complete_specification.md`
- **Progress Report**: `doc/report/i18n_implementation_progress.md`

### Code References

- **Diagnostics Crate**: `src/diagnostics/`
- **i18n Crate**: `src/i18n/`
- **Catalogs**: `i18n/*.spl`, `i18n/*.ko.spl`
- **Conversion Helper**: `src/driver/src/diagnostics_conversion.rs`

### Error Message Locations

See exploration agent output above for comprehensive list of all error message locations in the codebase.

---

## Next Steps

### Immediate Actions

1. **Review this plan** with team/user
2. **Prioritize phases** based on impact
3. **Start with Phase 1** (extend catalogs) - lowest risk, high value
4. **Create tracking issues** for each phase
5. **Set up test infrastructure** before code changes

### Quick Wins

These can be done independently and provide immediate value:

1. **Document existing error codes** (E0001-E3005)
2. **Test current i18n system** with `--lang ko`
3. **Create error code reference** documentation
4. **Add more Korean translations** for existing codes
5. **Set up integration test framework**

---

## Appendix A: Example Conversion

### Before (Hardcoded)

```rust
// compiler/interpreter.rs:313
if binding.is_const {
    return Err(CompileError::Semantic(format!(
        "cannot assign to const '{}'",
        name
    )));
}
```

### After (i18n)

```rust
use simple_diagnostics::{Diagnostic, i18n::ctx1};

if binding.is_const {
    let ctx = ctx1("name", name);
    return Err(CompileError::from_diagnostic(
        Diagnostic::error_i18n("compiler", "E1016", &ctx)
            .with_span(span)
            .with_label(span, "cannot assign to constant")
            .with_help("use `var` instead of `val` to make it mutable")
    ));
}
```

### Catalog Entry (English)

```simple
# i18n/compiler.spl
"E1016": {
    "id": "E1016",
    "title": "Cannot Assign to Constant",
    "message": "cannot assign to const '{name}'",
    "label": "cannot assign to this constant",
    "help": "use `var` instead of `val` to make it mutable"
}
```

### Catalog Entry (Korean)

```simple
# i18n/compiler.ko.spl
"E1016": {
    "id": "E1016",
    "title": "상수에 할당할 수 없음",
    "message": "상수 '{name}'에 할당할 수 없습니다",
    "label": "이 상수에 할당할 수 없습니다",
    "help": "가변으로 만들려면 `val` 대신 `var`를 사용하세요"
}
```

### Output (English)

```
error[E1016]: cannot assign to const 'x'
  --> test.spl:5:1
   |
5  | x = 42
   | ^^^^^^ cannot assign to this constant
   |
   = help: use `var` instead of `val` to make it mutable
```

### Output (Korean)

```
오류[E1016]: 상수 'x'에 할당할 수 없습니다
  --> test.spl:5:1
   |
5  | x = 42
   | ^^^^^^ 이 상수에 할당할 수 없습니다
   |
   = 도움말: 가변으로 만들려면 `val` 대신 `var`를 사용하세요
```

---

## Appendix B: Error Code Mapping Template

Use this template when mapping existing errors to catalog IDs:

```rust
// Location: [file:line]
// Current: [current error message]
// Code: [error code]
// Context: [list of parameters]
// Catalog: [domain]
//
// Example:
// Location: compiler/interpreter.rs:313
// Current: format!("cannot assign to const '{}'", name)
// Code: E1016
// Context: name (variable name)
// Catalog: compiler
```

---

## Conclusion

The i18n infrastructure is **complete and production-ready**. The remaining work is systematic conversion of Rust error sites to use the catalog system. This plan provides a phased approach with clear deliverables, estimated timelines, and technical guidance.

**Recommended approach**: Start with Phase 1 (extend catalogs) to establish complete coverage, then proceed with compiler integration (Phase 2) as the highest-impact next step.
