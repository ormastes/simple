# Implementation Plan: Statistics, Warnings, and Doc Coverage Enhancements
## Date: 2026-02-14

## Overview

Comprehensive plan to enhance Simple language compiler with:
1. Enhanced documentation statistics
2. Compile-time warnings (closure capture, ignored returns)
3. Group comment detection
4. Generic syntax support verification

---

## ✅ ALREADY COMPLETED (Verify Status)

### 1. Multiline Boolean with Parentheses ✅
- **File:** `test/unit/parser/multiline_bool_spec.spl` (143 lines, 18 tests)
- **Status:** PASSING
- **Solution:** Lexer suppresses newlines when `lex_paren_depth > 0`

### 2. Module Function Closures ✅
- **File:** `test/unit/runtime/module_closure_spec.spl` (85 lines, 10 tests)
- **Status:** PASSING
- **Finding:** Module closures WORK correctly (was documentation error)

### 3. Closure Capture Warning Infrastructure ✅
- **Implementation:** `src/core/closure_analysis.spl` (186 lines)
- **Tests:** `test/unit/compiler/closure_capture_warning_spec.spl` (177 lines, 25 tests)
- **Status:** PASSING (implementation complete)
- **Integration:** ⚠️ NOT integrated into compiler pipeline yet

### 4. Ignored Return Warning Infrastructure ✅
- **Implementation:** `src/core/interpreter/eval.spl` (has `eval_get_warnings()`)
- **Tests:** `test/unit/core/ignored_return_warning_spec.spl` (130 lines, 30 tests)
- **Status:** PASSING (implementation complete)
- **Integration:** ⚠️ NOT integrated into compiler pipeline yet

### 5. Generic Syntax Support ✅
- **Tests:** `test/unit/core/generic_syntax_spec.spl` (191 lines, 28 tests)
- **Status:** PASSING (parser supports `<>` syntax)
- **Parser:** `src/core/parser.spl` handles generics correctly

### 6. SDoctest Coverage Analysis ✅
- **Implementation:** `src/app/doc_coverage/analysis/sdoctest_coverage.spl` (544 lines)
- **Features:**
  - `compute_sdoctest_coverage()` - compares functions vs sdoctest blocks
  - `suggest_missing_tags()` - auto-suggests tags (stdlib:*, core:*, feature:*)
  - `validate_tag_format()` - validates "category:name" format
- **Status:** PRODUCTION READY
- **Integration:** ⚠️ NOT integrated into CLI yet

---

## 🔨 NEW FEATURES TO IMPLEMENT

### Feature 1: Inline Comment Coverage Detection

**Requirement:** Count functions/classes without inline comments, emit compile warnings

**Design:**
```simple
# In: src/app/doc_coverage/analysis/inline_comment_coverage.spl

struct InlineCommentResult:
    item_name: text
    item_kind: text  # "function", "class", "struct", etc.
    file_path: text
    line: i64
    has_inline_comment: bool
    has_docstring: bool
    has_sdoctest: bool
    warning_level: text  # "none", "info", "warn", "error"

fn compute_inline_comment_coverage(files: [text]) -> [InlineCommentResult]:
    # For each file:
    # 1. Scan for function/class/struct/enum declarations
    # 2. Check if inline comment exists on same line or line before
    # 3. Check if docstring exists (""" block)
    # 4. Check if sdoctest exists
    # 5. Determine warning level:
    #    - No inline, no docstring, no sdoctest = "error"
    #    - No inline, has docstring = "warn"
    #    - No inline, has sdoctest = "info"
    #    - Has inline = "none"
    pass_todo

fn emit_missing_comment_warnings(results: [InlineCommentResult]) -> [text]:
    # Generate warning messages for compiler output
    # Format: "warning: function 'foo' at file.spl:42 has no inline comment"
    pass_todo

fn generate_coverage_report(results: [InlineCommentResult]) -> text:
    # Generate markdown report:
    # - Total items scanned
    # - Items with inline comments (%)
    # - Items with docstrings (%)
    # - Items with sdoctest (%)
    # - Breakdown by file/module
    pass_todo
```

**Integration Points:**
1. CLI command: `bin/simple build doc-coverage --warn-missing-comments`
2. Test runner: Optional flag `--doc-warnings` to show during test runs
3. Output format: Same as other warnings (can be suppressed with `--no-doc-warnings`)

**Test File:** `test/unit/app/doc_coverage/inline_comment_coverage_spec.spl`

**Example Warnings:**
```
warning: function 'compute_result' at src/std/math.spl:42 has no inline comment
info: class 'Parser' at src/core/parser.spl:89 has sdoctest but no inline comment
error: public function 'api_call' at src/std/http.spl:156 has no documentation
```

---

### Feature 2: Group Comment Detection

**Requirement:** Detect consecutive const/var declarations without empty line, suggest adding group comment

**Design:**
```simple
# In: src/app/doc_coverage/analysis/group_comment_detection.spl

struct VariableGroup:
    file_path: text
    start_line: i64
    end_line: i64
    var_names: [text]
    var_count: i64
    has_group_comment: bool
    suggested_comment: text

fn detect_variable_groups(file_path: text, source: text) -> [VariableGroup]:
    # Scan for consecutive var/val declarations:
    # 1. Find lines with "var NAME" or "val NAME" pattern
    # 2. Group consecutive lines (no empty lines between)
    # 3. Check if comment exists before first line or on first line
    # 4. Groups of 3+ variables without comment = suggest adding one
    pass_todo

fn suggest_group_comment(group: VariableGroup) -> text:
    # Auto-generate suggested comment based on variable names
    # Example: var user_id, user_name, user_email
    # Suggests: "# User information fields"
    #
    # Use heuristics:
    # - Common prefix (user_*) → "User ..."
    # - All UPPER_CASE → "Constants for ..."
    # - Mixed → "Configuration values"
    pass_todo

fn emit_group_comment_warnings(groups: [VariableGroup]) -> [text]:
    # Generate warnings:
    # "info: 3 consecutive variables at file.spl:10-12 could use group comment"
    # "  suggestion: # User information fields"
    pass_todo
```

**Tag Naming Suggestions:**
- `group_comment:present` - Has group comment
- `group_comment:missing` - Missing group comment
- `group_comment:suggested` - Auto-suggested comment
- `var_group:config` - Configuration variables
- `var_group:state` - State variables
- `var_group:constants` - Constant values

**Integration:**
- CLI: `bin/simple build doc-coverage --check-group-comments`
- Output includes suggested comment text
- Optional auto-fix: `bin/simple fix --add-group-comments`

**Test File:** `test/unit/app/doc_coverage/group_comment_detection_spec.spl`

**Example Output:**
```
info: 4 consecutive variables at src/app/config.spl:23-26 could use group comment
  variables: db_host, db_port, db_name, db_user
  suggestion: # Database connection configuration
```

---

### Feature 3: Public Function vs SDoctest Comparison (Enhancement)

**Status:** Infrastructure exists in `sdoctest_coverage.spl`, needs CLI integration

**Required Changes:**

1. **Add CLI command:**
```bash
bin/simple build doc-coverage --sdoctest-report
```

2. **Output format:**
```
SDoctest Coverage Report
========================

Total public functions: 247
Functions with sdoctest: 89 (36%)
Missing sdoctest: 158 (64%)

By Module:
  std.string:   12/20 (60%)  ✅ Good
  std.array:     8/15 (53%)  ⚠️  Needs work
  std.math:      5/25 (20%)  ❌ Critical
  core.parser:   0/42 (0%)   ❌ Critical

Missing sdoctest tags suggested:
  - stdlib:string:split
  - stdlib:array:filter
  - core:parser:parse_expr
  [... full list ...]

Run with --tag-file=tags.txt to save suggested tags
```

3. **Tag file format (tags.txt):**
```
stdlib:string:split
stdlib:string:join
stdlib:array:map
stdlib:array:filter
core:parser:parse_expr
core:lexer:lex_token
```

**Test File:** `test/unit/app/doc_coverage/sdoctest_comparison_spec.spl`

**Integration:** Reuse `compute_sdoctest_coverage()` from existing code

---

## 🔌 INTEGRATION TASKS

### Task 1: Integrate Closure Capture Warnings into Compiler

**Current Status:** Implementation complete, not integrated

**Integration Points:**

1. **Parser Integration** (`src/core/parser.spl`):
```simple
# After parse_module() completes:
use core.closure_analysis.{analyze_closure_capture, closure_warnings_get}

fn parse_module(code: text, filename: text):
    # ... existing parsing ...

    # Run closure analysis
    analyze_closure_capture()

    # Warnings retrieved later by compiler/test runner
```

2. **Test Runner Integration** (`src/app/test_runner_new/test_runner_main.spl`):
```simple
use core.closure_analysis.{closure_warnings_get, closure_warnings_clear}

fn run_test_file(path: text):
    # Before running test:
    closure_warnings_clear()

    # After test completes:
    val warnings = closure_warnings_get()
    if warnings.len() > 0:
        for w in warnings:
            print "  [CLOSURE WARNING] {w}"
```

3. **CLI Integration** (`src/app/cli/main.spl`):
```simple
# Add flag: --no-closure-warnings to suppress
# Add flag: --closure-warnings-as-errors to fail on warnings
```

**Test Verification:**
- Run existing `closure_capture_warning_spec.spl` - should still pass
- Run manual test with known closure capture issue - should show warning
- Verify warnings appear in test output

---

### Task 2: Integrate Ignored Return Warnings into Evaluator

**Current Status:** Implementation exists in eval.spl, needs activation

**Integration Points:**

1. **Evaluator** (`src/core/interpreter/eval.spl`):
```simple
# Already has eval_get_warnings() - just needs activation in eval_function_call()

fn eval_function_call(fn_name: text, args: [Value]) -> Value:
    # ... existing logic ...

    val return_type = get_function_return_type(fn_name)
    val result = # ... call function ...

    # Check if result is used
    if not is_result_used() and return_type != "void" and return_type != "()":
        val warning = "warning: return value of type '{return_type}' from function '{fn_name}' is ignored"
        eval_warnings_add(warning)

    result
```

2. **Test Runner Integration** (same as above):
```simple
fn run_test_file(path: text):
    eval_reset()

    # ... run test ...

    val warnings = eval_get_warnings()
    for w in warnings:
        print "  [RETURN WARNING] {w}"
```

**Test Verification:**
- Run `ignored_return_warning_spec.spl` - all 30 tests should pass
- Create manual test with ignored return - should warn

---

### Task 3: Integrate Doc Coverage into CLI

**Required Files:**

1. **CLI Command** (`src/app/cli/doc_coverage_command.spl`):
```simple
use app.doc_coverage.analysis.sdoctest_coverage.{compute_sdoctest_coverage}
use app.doc_coverage.analysis.inline_comment_coverage.{compute_inline_comment_coverage}
use app.doc_coverage.analysis.group_comment_detection.{detect_variable_groups}

fn handle_doc_coverage_command(args: [text]):
    val flags = parse_flags(args)

    if flags.contains("--sdoctest-report"):
        run_sdoctest_report(flags)

    if flags.contains("--inline-comments"):
        run_inline_comment_check(flags)

    if flags.contains("--group-comments"):
        run_group_comment_check(flags)

    if flags.contains("--all"):
        run_sdoctest_report(flags)
        run_inline_comment_check(flags)
        run_group_comment_check(flags)
```

2. **CLI Main** (`src/app/cli/main.spl`):
```simple
# Add to command dispatch:
match command:
    case "doc-coverage":
        handle_doc_coverage_command(args)
```

3. **Help Text Update:**
```
bin/simple build doc-coverage [options]

Options:
  --sdoctest-report           Compare public functions vs sdoctest coverage
  --inline-comments           Check for missing inline comments
  --group-comments            Detect variable groups needing comments
  --all                       Run all doc coverage checks
  --warn-missing-comments     Emit warnings for missing comments
  --tag-file=FILE             Save suggested sdoctest tags to file
  --format=text|json|html     Output format (default: text)
```

---

## 📋 IMPLEMENTATION PHASES

### Phase 1: Verification & Integration (Priority: HIGH)
**Time Estimate:** 2-3 hours

**Tasks:**
1. ✅ Verify all existing tests pass (DONE - seen in exploration)
2. ⚠️ Integrate closure warnings into parser (needs implementation)
3. ⚠️ Integrate ignored return warnings into eval (needs implementation)
4. ⚠️ Update test runner to display warnings (needs implementation)
5. ⚠️ Add CLI flags for warning control (needs implementation)

**Deliverables:**
- Warnings appear in test runner output
- CLI flags to enable/disable warnings
- Documentation updated (CLAUDE.md, MEMORY.md)

**Test Command:**
```bash
bin/simple test test/unit/ --closure-warnings --return-warnings
```

---

### Phase 2: Inline Comment Coverage (Priority: MEDIUM)
**Time Estimate:** 3-4 hours

**Tasks:**
1. Create `inline_comment_coverage.spl` (250-300 lines)
2. Implement comment detection logic
3. Implement warning level determination
4. Create test file (150+ lines, 20+ tests)
5. Integrate into CLI

**Deliverables:**
- `src/app/doc_coverage/analysis/inline_comment_coverage.spl`
- `test/unit/app/doc_coverage/inline_comment_coverage_spec.spl`
- CLI command: `bin/simple build doc-coverage --inline-comments`
- Warning output in test runs (optional flag)

**Test Command:**
```bash
bin/simple build doc-coverage --inline-comments --warn-missing-comments
```

---

### Phase 3: Group Comment Detection (Priority: LOW)
**Time Estimate:** 3-4 hours

**Tasks:**
1. Create `group_comment_detection.spl` (200-250 lines)
2. Implement variable group detection
3. Implement comment suggestion heuristics
4. Create test file (100+ lines, 15+ tests)
5. Integrate into CLI

**Deliverables:**
- `src/app/doc_coverage/analysis/group_comment_detection.spl`
- `test/unit/app/doc_coverage/group_comment_detection_spec.spl`
- CLI command: `bin/simple build doc-coverage --group-comments`
- Auto-suggestion output

**Test Command:**
```bash
bin/simple build doc-coverage --group-comments
bin/simple fix --add-group-comments  # Future: auto-fix
```

---

### Phase 4: SDoctest CLI Integration (Priority: HIGH)
**Time Estimate:** 1-2 hours

**Tasks:**
1. Create `doc_coverage_command.spl` (150-200 lines)
2. Integrate with existing `sdoctest_coverage.spl`
3. Add tag file export
4. Add JSON/HTML output formats
5. Update help text

**Deliverables:**
- `src/app/cli/doc_coverage_command.spl`
- CLI command: `bin/simple build doc-coverage --sdoctest-report`
- Tag file export: `--tag-file=tags.txt`
- JSON export: `--format=json > coverage.json`

**Test Command:**
```bash
bin/simple build doc-coverage --sdoctest-report --tag-file=missing_tags.txt
```

---

## 🧪 TESTING STRATEGY

### Test Files to Create/Update

1. **Existing (Verify):**
   - `test/unit/compiler/closure_capture_warning_spec.spl` (177 lines) ✅
   - `test/unit/core/ignored_return_warning_spec.spl` (130 lines) ✅
   - `test/unit/core/generic_syntax_spec.spl` (191 lines) ✅
   - `test/unit/runtime/module_closure_spec.spl` (85 lines) ✅
   - `test/unit/parser/multiline_bool_spec.spl` (143 lines) ✅

2. **New (Create):**
   - `test/unit/app/doc_coverage/inline_comment_coverage_spec.spl` (150+ lines)
   - `test/unit/app/doc_coverage/group_comment_detection_spec.spl` (100+ lines)
   - `test/unit/app/doc_coverage/sdoctest_comparison_spec.spl` (100+ lines)
   - `test/unit/app/cli/doc_coverage_command_spec.spl` (120+ lines)

### Integration Tests

Create `test/integration/warnings_integration_spec.spl`:
```simple
describe "warning system integration":
    it "shows closure warnings in test output"
    it "shows ignored return warnings in test output"
    it "respects --no-closure-warnings flag"
    it "respects --no-return-warnings flag"
    it "combines multiple warning types"
```

Create `test/integration/doc_coverage_integration_spec.spl`:
```simple
describe "doc coverage CLI integration":
    it "generates sdoctest report"
    it "exports tag file"
    it "checks inline comments"
    it "detects variable groups"
    it "combines all checks with --all flag"
```

---

## 📊 SUCCESS METRICS

### Phase 1 Success Criteria:
- ✅ All 4,067+ existing tests still pass
- ✅ Closure warnings appear in test output (can be demonstrated)
- ✅ Ignored return warnings appear in test output
- ✅ CLI flags control warning display
- ✅ Documentation updated

### Phase 2 Success Criteria:
- ✅ Inline comment coverage reports generated
- ✅ Warnings emitted for missing comments
- ✅ Coverage percentage calculated correctly
- ✅ 20+ tests passing

### Phase 3 Success Criteria:
- ✅ Variable groups detected correctly
- ✅ Comment suggestions generated
- ✅ Heuristics work for common patterns
- ✅ 15+ tests passing

### Phase 4 Success Criteria:
- ✅ SDoctest report shows coverage percentage
- ✅ Tag file exports correctly
- ✅ JSON output valid and complete
- ✅ Help text comprehensive

---

## 🚀 EXECUTION PLAN (Multi-Agent)

### Agent Assignments

**Agent 1: Integration Specialist** (code agent)
- Task: Integrate closure warnings into parser
- Task: Integrate ignored return warnings into eval
- Task: Update test runner for warning display
- Files: `src/core/parser.spl`, `src/core/interpreter/eval.spl`, `src/app/test_runner_new/test_runner_main.spl`

**Agent 2: Doc Coverage Specialist** (infra agent)
- Task: Implement inline comment coverage
- Task: Implement group comment detection
- Files: `src/app/doc_coverage/analysis/*.spl`

**Agent 3: CLI Specialist** (code agent)
- Task: Create doc coverage CLI command
- Task: Add help text and flag parsing
- Files: `src/app/cli/doc_coverage_command.spl`, `src/app/cli/main.spl`

**Agent 4: Test Specialist** (test agent)
- Task: Create new test files for doc coverage features
- Task: Create integration tests
- Files: `test/unit/app/doc_coverage/*.spl`, `test/integration/*.spl`

**Agent 5: Verification Specialist** (test agent)
- Task: Run full test suite after each phase
- Task: Verify no regressions
- Task: Document results

### Parallel Execution Strategy

**Batch 1 (Parallel - Can run simultaneously):**
- Agent 1: Parser integration (closure warnings)
- Agent 2: Inline comment coverage implementation
- Agent 3: CLI command structure

**Batch 2 (Parallel - After Batch 1):**
- Agent 1: Eval integration (ignored return warnings)
- Agent 2: Group comment detection implementation
- Agent 4: Test file creation (doc coverage)

**Batch 3 (Sequential - After Batch 2):**
- Agent 3: CLI integration of all features
- Agent 4: Integration test creation
- Agent 5: Full verification

---

## 📝 DOCUMENTATION UPDATES

### Files to Update:

1. **MEMORY.md:**
   - Add: "Closure capture warnings active (compiler integration)"
   - Add: "Ignored return warnings active (eval integration)"
   - Add: "Doc coverage CLI commands available"
   - Add: "Inline comment coverage checking"
   - Add: "Variable group comment detection"

2. **CLAUDE.md:**
   - Add warnings section to "Critical Rules"
   - Document CLI commands in "Quick Commands"
   - Add to "Features" list

3. **New Documentation:**
   - `doc/guide/compiler_warnings.md` - All warning types, suppression
   - `doc/guide/doc_coverage.md` - Using doc coverage tools
   - `doc/guide/code_quality.md` - Best practices for comments, docs

4. **Feature Tracking:**
   - Add to `doc/feature/feature.md` when complete
   - Update `doc/feature/feature_db.sdn` with new features

---

## 🔍 VALIDATION CHECKLIST

Before marking complete:

- [ ] All existing tests pass (4,067+)
- [ ] New tests pass (estimated +50 tests)
- [ ] Warnings appear in test runner output
- [ ] CLI commands work as documented
- [ ] Help text complete and accurate
- [ ] No performance regressions
- [ ] Documentation updated (MEMORY.md, CLAUDE.md)
- [ ] Code formatted and linted
- [ ] Manual testing performed
- [ ] Integration tests pass
- [ ] User guide created

---

## 📅 TIMELINE ESTIMATE

**Total Time:** 12-15 hours

**Phase 1:** 2-3 hours (Integration)
**Phase 2:** 3-4 hours (Inline comment coverage)
**Phase 3:** 3-4 hours (Group comment detection)
**Phase 4:** 1-2 hours (CLI integration)
**Testing & Verification:** 2-3 hours
**Documentation:** 1-2 hours

**Suggested Schedule:**
- Day 1 AM: Phase 1 (Integration) - Agents 1, 3
- Day 1 PM: Phase 2 (Inline comments) - Agents 2, 4
- Day 2 AM: Phase 3 (Group comments) - Agents 2, 4
- Day 2 PM: Phase 4 (CLI) + Verification - Agents 3, 5

---

## 🎯 NEXT IMMEDIATE ACTIONS

1. ✅ Verify all existing tests pass (DONE in exploration)
2. ⚠️ Spawn Agent 1 to integrate closure warnings
3. ⚠️ Spawn Agent 2 to implement inline comment coverage
4. ⚠️ Spawn Agent 3 to create CLI command structure
5. ⚠️ Run verification after each batch completes

---

**Status:** Ready to begin implementation
**Priority Order:** Phase 1 → Phase 4 → Phase 2 → Phase 3
**Blockers:** None (all dependencies resolved)
