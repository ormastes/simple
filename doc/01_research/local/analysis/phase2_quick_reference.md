# Phase 2: Cross-Module Duplication - Quick Reference

**Generated:** 2026-02-14
**Analysis:** Manual inspection of ~30 representative files
**Scope:** src/core, src/compiler, src/lib, src/lib, src/app

---

## Top 7 Duplication Patterns

| # | Pattern | Locations | Est. Lines | Impact | Priority |
|---|---------|-----------|------------|--------|----------|
| 1 | Backend type definitions | 2 files | 400 | Critical | P1 |
| 2 | Configuration parsers | 7+ files | 1,200-1,500 | High | P1 |
| 3 | String utilities | 4 files | 250-300 | High | P1 |
| 4 | Error handling | 3 files | 150-200 | Medium | P2 |
| 5 | Integer conversion | 2+ files | 60-70 | Medium | P2 |
| 6 | Loop patterns | 244 files | N/A* | Low | P3 |
| 7 | Type wrappers | Scattered | 50-100† | Low | P3 |

*Language limitation workaround, not refactorable
†Prevention of future duplication

**Total removable duplication:** 2,060-2,470 lines (~4-5% of codebase)

---

## One-Page Action Items

### Immediate (This Week)

**1. Backend Types Unification** (2-3 hours)
```bash
# Keep: src/compiler_core/backend_types.spl
# Delete: src/compiler/backend/backend_types.spl
# Update all imports: compiler.backend.backend_types → core.backend_types
```
**Saves:** 400 lines

**2. Config Parser Creation** (6-7 hours)
```bash
# Create: src/lib/config_parser.spl (base parser)
# Migrate: 7 config files to use new parser
# Test: Ensure existing configs load unchanged
```
**Saves:** 1,200-1,500 lines

### Near Term (Next 2 Weeks)

**3. String Utilities** (3-4 hours)
```bash
# Create: src/lib/string_core.spl (canonical implementations)
# Update: src/compiler_core/types.spl to re-export
# Cleanup: src/lib/template/utilities.spl duplicates
```
**Saves:** 250-300 lines

**4. Error Handling** (3-4 hours)
```bash
# Create: src/lib/error_core.spl (base trait)
# Create: src/lib/error_format.spl (formatters)
# Migrate: 3 error modules to use shared base
```
**Saves:** 150-200 lines

### Documentation Only

**5. Loop Patterns**
- Document `while i < arr.len()` as acceptable pattern
- Note: Runtime limitation (nested closure capture)
- Add to style guide

**6. Semantic Types**
- Move `src/lib/types.spl` → `src/lib/semantic_types.spl`
- Organize by category (IDs, Sizes, Time, etc.)
- Update imports

---

## File Inventory

### Duplicated Backend Types
- `src/compiler_core/backend_types.spl` (158 lines) ← KEEP
- `src/compiler/backend/backend_types.spl` (~400 lines) ← DELETE

### Duplicated String Functions
- `src/compiler_core/types.spl` (lines 14-48)
- `src/lib/text.spl` (char_code lookup)
- `src/lib/template/utilities.spl` (lines 40-180)
- `doc/analysis/stdlib_utils_concatenated.spl` (11,917+)

### Duplicated Config Parsers
1. `src/app/duplicate_check/config.spl` (106 lines)
2. `src/app/test_runner_new/sdoctest/config.spl` (~60 lines)
3. `src/app/build/config.spl` (~100 lines)
4. `src/app/test/cpu_aware_test.spl` (~40 lines)
5. `src/app/mcp/fileio_protection.spl` (~80 lines)
6. `src/lib/sdn/parser.spl` (~150 lines)
7. `src/lib/src/dl/config_loader.spl` (~70 lines)

### Duplicated Error Handlers
- `src/compiler_core/error.spl` (easyfix suggestions, 158 lines)
- `src/lib/error.spl` (trait hierarchy, 100+ lines)
- `src/compiler/backend/codegen_errors.spl` (enum + struct, 100+ lines)

---

## Quick Commands

### Analysis
```bash
# Count duplicated string functions
grep -rn "^fn str_" src/ | wc -l

# Find config parsers
grep -rn "fn.*parse.*config" src/ | head -20

# Count while loops (manual iteration pattern)
grep -r "while.*\.len()" src/{core,compiler,std,lib}/ | wc -l
```

### Before Refactoring
```bash
# Backup
jj new -m "wip: refactoring [item]"

# Baseline tests
bin/simple test > /tmp/baseline.txt

# Line counts
wc -l src/compiler_core/backend_types.spl
wc -l src/compiler/backend/backend_types.spl
```

### After Refactoring
```bash
# Test
bin/simple test > /tmp/after.txt
diff /tmp/baseline.txt /tmp/after.txt

# Verify imports
grep -r "use.*old_module" src/

# Measure savings
wc -l [new files]
```

---

## Common Anti-Patterns

### 1. Manual Loop Iteration
```simple
# Repeated pattern (955 occurrences)
var i = 0
while i < arr.len():
    val item = arr[i]
    process(item)
    i = i + 1

# Prefer: for-each when possible
for item in arr:
    process(item)
```

### 2. Quote Stripping
```simple
# Repeated pattern (15+ implementations)
var clean_value = ""
var i = 0
while i < value.len():
    val ch = value[i:i+1]
    if ch != "\"" and ch != "'":
        clean_value = clean_value + ch
    i = i + 1

# Shared utility:
fn strip_quotes(s: text) -> text:
    # Single canonical implementation
```

### 3. Integer-to-String
```simple
# 70-line manual implementation (multiple files)
fn int_to_str(n: i64) -> text:
    if n == 0: return "0"
    # ... 60+ lines of digit mapping ...

# Investigate runtime built-in:
fn int_to_str(n: i64) -> text:
    text(n)  # Or rt_int_to_str(n)
```

---

## Success Metrics

### Code Reduction
- **Target:** 2,000+ lines removed
- **Method:** Line count before/after each refactoring
- **Tracking:** Update this doc with actual savings

### Test Coverage
- **Requirement:** 100% test pass rate maintained
- **Method:** `bin/simple test` before and after
- **Baseline:** 4,067/4,067 tests passing (current)

### Import Consolidation
- **Goal:** Reduce import paths by 50% for refactored modules
- **Example:** 10 config parsers → 1 shared parser = 9 fewer implementations

---

## Risk Assessment

### Low Risk (Safe to proceed)
- Backend types unification (identical enum variants)
- String utilities (backwards-compatible re-exports)
- Semantic types registry (just moving file)

### Medium Risk (Requires careful testing)
- Config parser migration (behavior must match exactly)
- Error handling consolidation (new trait implementations)

### High Risk (Investigate first)
- Integer conversion (check runtime capabilities)
- Loop pattern changes (runtime limitation)

---

## Team Coordination

### Before Starting
- [ ] Review analysis with team
- [ ] Prioritize items (confirm P1/P2/P3)
- [ ] Assign ownership (who does what)
- [ ] Schedule implementation sprints

### During Refactoring
- [ ] Create feature branch for each item
- [ ] Run tests before and after
- [ ] Update this doc with progress
- [ ] Communicate blockers immediately

### After Completion
- [ ] Update developer guide
- [ ] Document new shared libraries
- [ ] Add linter rules (prevent future duplication)
- [ ] Celebrate 2,000+ line reduction!

---

## References

- **Full Analysis:** `doc/analysis/phase2_crossmodule_duplicates.md`
- **Implementation Plan:** `doc/analysis/phase2_shared_library_plan.md`
- **Phase 1 Results:** `doc/analysis/phase1_duplicate_scan_results.md` (if exists)

---

**End of Quick Reference**
