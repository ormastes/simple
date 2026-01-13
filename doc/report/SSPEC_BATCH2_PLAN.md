# SSpec Batch 2 - Migration Plan

**Date:** 2026-01-13 (Continuation Session)
**Initiative:** SSpec Documentation Initiative
**Batch:** Batch 2 (Next 10 smallest test files)
**Status:** 🚀 Starting

---

## Overview

Following the successful completion of Batch 1 (7/10 files with comprehensive documentation), Batch 2 will migrate the next set of small test files to the SSpec format with comprehensive documentation.

---

## Batch 2 File Selection

**Selection Criteria:** Next 10 smallest test files (by current line count) that haven't been migrated yet.

| # | File | Category | Lines | TODOs | Status |
|---|------|----------|-------|-------|--------|
| 1 | structs_spec.spl | Language | 205 | 0 | Old format |
| 2 | option_result_spec.spl | Types | 205 | 0 | Old format |
| 3 | match_spec.spl | Control Flow | 207 | 0 | Old format |
| 4 | basic_types_spec.spl | Types | 207 | 0 | Old format |
| 5 | strings_spec.spl | Data Structures | 208 | 0 | Old format |
| 6 | variables_spec.spl | Language | 217 | 0 | Old format |
| 7 | loops_spec.spl | Control Flow | 220 | 0 | Old format |
| 8 | torch_caching_spec.spl | ML | 220 | 44 | Old format (planned feature?) |
| 9 | functions_spec.spl | Language | 222 | 0 | Old format |
| 10 | classes_spec.spl | Language | 225 | 0 | Old format |

**Total Lines (Before):** 2,116 lines
**Estimated After (4.4x growth):** ~9,300 lines

---

## Migration Strategy

### Phase 1: Automated Migration (Est. 1-2 hours)
Use the automated migration script to convert all 10 files from old format to SSpec format:
- Convert print statements to describe/it blocks
- Convert if/else assertions to expect() syntax
- Add TODO placeholders for docstrings

**Expected Outcome:** All 10 files in SSpec structure with TODOs

### Phase 2: Manual Documentation (Est. 6-8 hours)
Add comprehensive documentation following Batch 1 patterns:
1. File-level docstrings (~150-200 lines each)
2. Describe block docstrings (~25-40 lines each)
3. It block docstrings with Given/When/Then (~40-60 lines each)

**Prioritization:**
- **High Priority (Core Features):** structs, basic_types, variables, functions, classes, match, strings
- **Medium Priority:** loops, option_result
- **Investigation Needed:** torch_caching (44 TODOs - might be planned feature)

---

## Documentation Template Reference

### File-Level Docstring Structure
```simple
"""
# [Feature Name]

**Feature ID:** #[ID]
**Category:** [Category]
**Difficulty:** [1-5]
**Status:** [Complete|In Progress|Planned]

## Overview
[Feature description, purpose, use cases]

## Syntax
[Grammar rules, code examples]

## Runtime Representation
[Internal implementation details, Rust types]

## Comparison with Other Languages
[Table comparing Simple vs Python/JS/Rust]

## Common Patterns
[Usage patterns, best practices]

## Implementation Files
[References to source files]
"""
```

### Describe Block Docstring
```simple
describe "[Feature Area]":
    """
    ## [Feature Area Title]

    [Technical overview]

    **Grammar:** [rules]
    **Key Properties:** [list]
    **Implementation:** [file references]
    """
```

### It Block Docstring
```simple
it "[test description]":
    """
    **Given** [initial state]
    **When** [action]
    **Then** [expected outcome]

    **Code Example:** [comprehensive example]
    **Runtime Behavior:** [details]
    **Implementation:** [file references]
    **Related Features:** [cross-references]
    **Common Patterns:** [patterns]
    """
```

---

## Estimated Metrics

### Time Estimates
- **Automated Migration:** 1-2 hours for all 10 files
- **Manual Documentation:**
  - First file (learning/template): ~1.5 hours
  - Subsequent files: ~45-60 minutes each
  - Total: ~8-10 hours

**Total Time:** ~10-12 hours

### Documentation Growth
Based on Batch 1 average growth of +440%:
- **Before:** 2,116 lines
- **After:** ~9,300 lines
- **Growth:** +7,200 lines (+340%)

### Quality Targets
- ✅ All assertions converted to expect() syntax
- ✅ Comprehensive file-level docstrings
- ✅ Given/When/Then format for all it blocks
- ✅ Code examples for all major features
- ✅ Implementation file references
- ✅ Cross-references to related features

---

## Success Criteria

**Batch 2 Complete When:**
1. All 10 files migrated to SSpec format
2. All implemented features have comprehensive documentation
3. 0 TODOs in core feature files (structs, basic_types, variables, functions, classes, match, strings, loops, option_result)
4. torch_caching_spec.spl assessed (document if implemented, mark as planned if not)
5. All commits pushed to main
6. Completion report created

---

## Risk Assessment

### Low Risk
- Files are small (205-225 lines)
- Old format is well-understood
- Automated migration proven successful in Batch 1
- Documentation patterns established

### Medium Risk
- torch_caching_spec.spl has 44 TODOs (might be planned feature requiring investigation)
- Parser still doesn't support SSpec syntax fully (files will be documentation artifacts)

### Mitigation
- Investigate torch_caching early in process
- Follow established documentation patterns
- Test migration on smallest file first
- Commit frequently

---

## Next Steps

1. ✅ Create Batch 2 plan (this document)
2. 🎯 Run automated migration on all 10 files
3. Verify migration output
4. Start manual documentation with smallest file (structs_spec.spl or option_result_spec.spl)
5. Continue through batch following prioritization
6. Create Batch 2 completion report

---

**Plan Created:** 2026-01-13
**Status:** Ready to Execute
**Dependencies:** Batch 1 completion ✅
**Expected Completion:** Same session or next session
