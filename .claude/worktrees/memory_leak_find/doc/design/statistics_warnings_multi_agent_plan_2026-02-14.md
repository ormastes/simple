# Multi-Agent Implementation Plan: Statistics & Warnings Enhancement
**Date:** 2026-02-14
**Status:** Ready for Execution
**Total Estimated Time:** 8-12 hours (immediate work) + 40-60 hours (generic types)

---

## Overview

Based on comprehensive analysis, **85% of requested features already exist**. This plan focuses on:
1. **Immediate enhancements** (3 features, 8-12 hours)
2. **Long-term project** (generic types, 40-60 hours)

---

## Phase 1: Immediate Enhancements (8-12 hours)

### Agent Assignment Strategy
- **Parallel execution** for independent features
- **Sequential verification** after each feature completes

---

### Task 1A: Inline Comment Absence Tracking
**Agent:** `code` (implementation) + `test` (testing)
**Priority:** High
**Estimated:** 3 hours
**Depends On:** None

#### Subtasks for `code` agent
1. **Enhance `inline_comment_coverage.spl`**
   - Add `count_functions_without_inline_comments(items: [DocItem]) -> i64`
   - Add `find_functions_without_comments(items: [DocItem]) -> [DocItem]`
   - Export new functions

2. **Update `src/app/stats/dynamic.spl`**
   - Modify `compute_doc_coverage()` to return 4-tuple:
     ```simple
     (total_public, documented, with_sdoctest, without_inline_comment)
     ```
   - Add stats output:
     ```
     No inline comments: 50 (20%)
     ```

3. **Update `src/app/stats/json_formatter.spl`**
   - Add `without_inline_comment` field to JSON output
   - Calculate `no_inline_percent`

#### Subtasks for `test` agent
1. **Create `test/unit/app/doc_coverage/inline_comment_absence_spec.spl`**
   - Test: `count_functions_without_inline_comments()` returns correct count
   - Test: Functions with `#` comments excluded
   - Test: Functions with docstrings but no inline comments counted
   - Test: Class methods counted separately from functions

2. **Update `test/unit/app/stats/stats_spec.spl`**
   - Test: JSON output includes `without_inline_comment`
   - Test: Text output shows "No inline comments" line
   - Test: Percentages calculated correctly

#### Verification
- Run: `bin/simple test test/unit/app/doc_coverage/inline_comment_absence_spec.spl`
- Run: `bin/simple stats` (verify output includes new metric)
- Run: `bin/simple stats --json | jq .documentation.without_inline_comment`

---

### Task 1B: Tag Suggestion CLI Integration
**Agent:** `code` (implementation) + `test` (testing)
**Priority:** High
**Estimated:** 4 hours
**Depends On:** None

#### Subtasks for `code` agent
1. **Create `src/app/cli/doc_coverage_command.spl`**
   ```simple
   fn run_doc_coverage_command(args: [text]):
       # Parses flags: --suggest-tags, --check-coverage, --threshold=N
       # Calls appropriate analysis functions
       # Emits formatted output
   ```

2. **Add subcommand to `src/app/cli/main.spl`**
   - Add `"doc-coverage"` to command dispatch
   - Call `run_doc_coverage_command(args)`

3. **Implement tag suggestion output**
   - Format: `file.spl:42: Missing tag for function 'parse_expr' → Suggested: core:parser`
   - Color coding (if terminal supports)
   - Summary: "Found 15 items missing tags"

#### Subtasks for `test` agent
1. **Create `test/unit/app/cli/doc_coverage_command_spec.spl`**
   - Test: `simple doc-coverage` runs without error
   - Test: `--suggest-tags` outputs suggested tags
   - Test: `--check-coverage` shows coverage percentage
   - Test: `--threshold=80` fails if below threshold
   - Test: Exit code 0 for success, 1 for below threshold

2. **Integration test**
   - Create test fixture file with missing documentation
   - Run `simple doc-coverage --suggest-tags`
   - Verify expected tags appear in output

#### CLI Examples
```bash
# Show all coverage metrics
bin/simple doc-coverage

# Suggest tags for undocumented items
bin/simple doc-coverage --suggest-tags

# Check coverage meets threshold
bin/simple doc-coverage --threshold=80

# Combine with JSON output
bin/simple doc-coverage --json --suggest-tags
```

#### Verification
- Run: `bin/simple doc-coverage --help`
- Run: `bin/simple doc-coverage --suggest-tags`
- Run: `bin/simple test test/unit/app/cli/doc_coverage_command_spec.spl`

---

### Task 1C: Build System Warning Integration
**Agent:** `code` (implementation) + `infra` (build system)
**Priority:** High
**Estimated:** 4 hours
**Depends On:** None

#### Subtasks for `code` agent
1. **Update `src/app/build/config.spl`**
   - Add flags: `warn_docs: bool`, `warn_closure: bool`, `warn_ignored: bool`
   - Parse from command-line args

2. **Update `src/app/build/main.spl`**
   - Before compilation, call warning checks if flags enabled
   - Emit warnings to stderr
   - Track warning count

3. **Create `src/app/build/doc_warnings.spl`**
   ```simple
   fn emit_documentation_warnings(files: [text], config: BuildConfig):
       # Scans all files for missing docs
       # Calls doc_coverage.compiler_warnings functions
       # Emits formatted warnings
   ```

#### Subtasks for `infra` agent
1. **Update `src/app/build/orchestrator.spl`**
   - Hook warning emission into build pipeline
   - Run after parsing, before codegen
   - Accumulate warnings across all files

2. **Add warning summary**
   - After build completes: "Build succeeded with 15 warnings"
   - Option: `--warn-as-error` treats warnings as errors (exit code 1)

#### CLI Examples
```bash
# Enable documentation warnings
bin/simple build --warn-docs

# Enable all warnings
bin/simple build --warn-all

# Treat warnings as errors
bin/simple build --warn-docs --warn-as-error

# Show only closure warnings
bin/simple build --warn-closure
```

#### Verification
- Run: `bin/simple build --warn-docs` (should show warnings)
- Run: `bin/simple build --warn-closure` (should detect closure captures)
- Run: `bin/simple build --warn-all` (should show all warning types)

---

### Task 1D: Update Documentation
**Agent:** `docs`
**Priority:** Medium
**Estimated:** 2 hours
**Depends On:** Tasks 1A, 1B, 1C completion

#### Deliverables
1. **Create `doc/guide/documentation_coverage.md`**
   - Overview of doc coverage system
   - How to use `simple doc-coverage` command
   - Interpreting coverage metrics
   - Tag naming conventions
   - Best practices

2. **Update `README.md`**
   - Add section: "Documentation Coverage"
   - Link to detailed guide
   - Add sdoctest examples for new features

3. **Update `CLAUDE.md`**
   - Add new CLI commands to Quick Commands section
   - Document warning flags

#### Verification
- Check: All examples run without errors
- Check: Links resolve correctly
- Check: Markdown renders properly

---

### Task 1E: Fix MEMORY.md Module Closure Claim
**Agent:** `docs`
**Priority:** Medium
**Estimated:** 1 hour
**Depends On:** None (independent)

#### Changes Required
1. **Update `MEMORY.md`** section "CRITICAL: Simple Language Limitations"
   - ❌ **Remove:** "Module function closures broken" claim
   - ✅ **Replace with:** "Module function closures work correctly (verified by tests)"
   - ✅ **Clarify:** "Issue was SIMPLE_LIB import path, not closures. Use symlinks."
   - ✅ **Add reference:** "See test/unit/runtime/module_closure_spec.spl for proof"

2. **Update `doc/report/import_system_update_2026-02-09.md`**
   - Add note that module closures were never the problem
   - Explain that closure capture limitation ONLY applies to nested functions

#### Verification
- Check: `test/unit/runtime/module_closure_spec.spl` all passing
- Check: No references to "broken module closures" in docs

---

## Phase 2: Long-Term Enhancement (40-60 hours)

### Task 2: Generic Type Support in Interpreter
**Agent:** `code` (primary) + `test` (testing) + `debug` (verification)
**Priority:** Low (separate epic)
**Estimated:** 40-60 hours
**Complexity:** High

#### Overview
Enable `<>` generic syntax in runtime parser and interpreter. Currently blocked by parser rejecting `<` as generic parameter start.

#### Subtasks for `code` agent

##### 2.1: Lexer Enhancement (8 hours)
1. **Context-aware `<` token**
   - Detect `<` after identifier as generic start
   - Track `<>` nesting depth (similar to paren depth)
   - Suppress newline tokens inside generic parameters

2. **New tokens**
   - `GENERIC_OPEN` for `<` in generic context
   - `GENERIC_CLOSE` for `>` in generic context
   - Distinguish from `LT`, `GT` comparison operators

3. **Lookahead logic**
   - `class Foo<` → GENERIC_OPEN
   - `x < y` → LT
   - `fn foo<` → GENERIC_OPEN
   - `a > b` → GT

##### 2.2: Parser Enhancement (12 hours)
1. **Generic parameter parsing**
   ```simple
   parse_generic_params():
       # <T, U, V> or <T: Trait>
       # Returns list of type parameter names
   ```

2. **Generic constraints**
   ```simple
   parse_generic_constraint():
       # T: Display + Clone
       # Returns list of trait bounds
   ```

3. **Update declaration parsing**
   - `parse_class_decl()` - support `class Foo<T>:`
   - `parse_fn_decl()` - support `fn map<T, U>(...):`
   - `parse_struct_decl()` - support `struct Pair<A, B>:`
   - `parse_enum_decl()` - support `enum Option<T>:`

##### 2.3: Type Checker Enhancement (10 hours)
1. **Generic type representation**
   ```simple
   struct GenericType:
       base_name: text
       type_params: [text]
       constraints: [text]
   ```

2. **Type parameter substitution**
   - Resolve `T` to concrete type at instantiation
   - Check constraint satisfaction

3. **Monomorphization**
   - Generate specialized version per concrete type
   - `Vec<i64>` and `Vec<text>` → separate implementations

##### 2.4: Interpreter Support (8 hours)
1. **Type erasure**
   - Option A: Erase generics at runtime (like Java)
   - Option B: Monomorphize during interpretation

2. **Generic function calls**
   - Infer type arguments from call site
   - Instantiate generic function with concrete types

3. **Generic data structures**
   - `Option<T>` works at runtime
   - Type checking deferred to runtime

##### 2.5: Error Messages (2 hours)
1. **Helpful errors**
   - "Type parameter T not in scope"
   - "Cannot infer type for generic parameter U"
   - "Type i64 does not satisfy constraint Display"

#### Subtasks for `test` agent

##### 2.6: Test Suite (10 hours)
1. **Create `test/unit/compiler_core/generic_types_spec.spl`**
   - 50+ tests covering all generic scenarios

2. **Test categories**
   - Generic classes: `class Box<T>`
   - Generic functions: `fn identity<T>(x: T) -> T`
   - Generic structs: `struct Pair<A, B>`
   - Generic enums: `enum Result<T, E>`
   - Nested generics: `Vec<Option<i64>>`
   - Multiple constraints: `fn sort<T: Ord + Clone>(...)`
   - Type inference: `identity(42)` infers `<i64>`

3. **Integration tests**
   - Use generics in real code (not just unit tests)
   - `src/lib/collections/vec.spl` - generic vector
   - `src/lib/option.spl` - generic option type

##### 2.7: Compiler Tests
1. **Update `test/unit/compiler/generic_template_spec.spl`**
   - Test compilation of generic code
   - Verify monomorphization produces correct output

#### Verification Strategy
1. **Incremental testing** - Test each phase separately
2. **Regression testing** - Ensure existing code still works
3. **Performance testing** - Measure monomorphization overhead

#### Risks and Mitigation
- **Risk:** Breaking existing parser
  - **Mitigation:** Feature flag `--enable-generics`, off by default
- **Risk:** Performance degradation
  - **Mitigation:** Monomorphization caching
- **Risk:** Complex error messages
  - **Mitigation:** Dedicated error formatter for generic errors

---

## Execution Strategy

### Parallel Execution Plan

#### Day 1 (Morning)
**Agents:** `code` (Task 1A), `code` (Task 1B), `docs` (Task 1E)
- All tasks are independent
- Can run in parallel
- Expected: 3 agents complete by EOD

#### Day 1 (Afternoon)
**Agents:** `test` (Task 1A tests), `test` (Task 1B tests), `infra` (Task 1C)
- Test agents verify morning's code
- Infra agent adds build system hooks

#### Day 2 (Morning)
**Agents:** `code` (Task 1C integration), `docs` (Task 1D)
- Finalize build system warnings
- Write user documentation

#### Day 2 (Afternoon)
**Agent:** `test` (integration testing)
- Run full test suite
- Verify all warnings work end-to-end
- Regression testing

### Phase 2 (Generics) - Separate Epic
- Create dedicated project plan
- Allocate 2-3 weeks
- Requires design review before implementation

---

## Monitoring and Verification

### Success Criteria
1. ✅ All new tests passing
2. ✅ Zero regressions in existing tests
3. ✅ CLI commands work as specified
4. ✅ Documentation complete and accurate
5. ✅ Performance impact < 5% on `simple stats`

### Verification Commands
```bash
# Run all new tests
bin/simple test test/unit/app/doc_coverage/
bin/simple test test/unit/app/cli/doc_coverage_command_spec.spl

# Run regression tests
bin/simple test

# Verify CLI works
bin/simple doc-coverage
bin/simple doc-coverage --suggest-tags
bin/simple stats
bin/simple build --warn-docs

# Performance check
time bin/simple stats
time bin/simple stats --quick
```

---

## Rollback Plan

If any task fails:
1. **Revert commits** - Use `jj undo` to rollback changes
2. **Isolate issue** - Run single test to identify failure
3. **Fix forward** - Prefer fixing over reverting if possible
4. **Document** - Add issue to bug tracker if unfixable

---

## Communication Protocol

### Agent Handoff
1. **Code → Test:** Provide test cases and expected behavior
2. **Test → Docs:** Report any API changes for documentation
3. **All → User:** Daily status update on progress

### Blocking Issues
- Report immediately if blocked
- Tag with `BLOCKED:` prefix
- Suggest alternatives or workarounds

---

## Resource Allocation

### Time Budget
- **Phase 1 (Immediate):** 8-12 hours over 2 days
- **Phase 2 (Generics):** 40-60 hours over 2-3 weeks

### Agent Allocation
- `code` agent: 40% of time (implementation heavy)
- `test` agent: 30% of time (extensive testing)
- `docs` agent: 15% of time (documentation)
- `infra` agent: 10% of time (build integration)
- `debug` agent: 5% of time (troubleshooting)

---

## Deliverables Checklist

### Phase 1 Deliverables
- [ ] `src/app/doc_coverage/analysis/inline_comment_coverage.spl` - Enhanced
- [ ] `src/app/stats/dynamic.spl` - Updated with inline comment tracking
- [ ] `src/app/stats/json_formatter.spl` - JSON field added
- [ ] `src/app/cli/doc_coverage_command.spl` - New file
- [ ] `src/app/build/doc_warnings.spl` - New file
- [ ] `src/app/build/config.spl` - Warning flags added
- [ ] `src/app/build/main.spl` - Warning integration
- [ ] `test/unit/app/doc_coverage/inline_comment_absence_spec.spl` - New tests
- [ ] `test/unit/app/cli/doc_coverage_command_spec.spl` - New tests
- [ ] `doc/guide/documentation_coverage.md` - New guide
- [ ] `README.md` - Updated
- [ ] `CLAUDE.md` - Updated
- [ ] `MEMORY.md` - Fixed module closure claim

### Phase 2 Deliverables (Future)
- [ ] `src/compiler_core/lexer.spl` - Generic-aware tokenization
- [ ] `src/compiler_core/parser.spl` - Generic syntax parsing
- [ ] `src/compiler_core/types.spl` - Generic type representation
- [ ] `src/compiler_core/interpreter/eval.spl` - Generic evaluation
- [ ] `test/unit/compiler_core/generic_types_spec.spl` - Comprehensive tests
- [ ] `src/lib/collections/vec.spl` - Generic vector example
- [ ] `src/lib/option.spl` - Generic option type
- [ ] `doc/guide/generic_types.md` - User guide

---

## Conclusion

This plan provides **clear, actionable steps** for completing the statistics and warnings enhancement. Phase 1 can be completed in **2 days with parallel agent execution**. Phase 2 (generics) is a **major feature requiring separate planning**.

**Next Step:** Execute Phase 1 tasks in parallel using multiple agents.

---

**Plan Date:** 2026-02-14
**Plan Author:** Claude Code
**Status:** Ready for Execution
**Review Required:** No (straightforward enhancements)
