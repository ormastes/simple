# Implementation Plan - Warnings & Generic Syntax
**Date:** 2026-02-14
**Status:** Ready for parallel execution

---

## Summary

Complete 3 major features using parallel agent execution:
1. Closure capture warnings (integration + tests)
2. Ignored return warnings (implementation)
3. Generic syntax parser (interpreter support)

---

## Agent Assignments

### Agent 1: `test` agent - Closure Capture Warning Tests
**Task:** Expand `test/unit/compiler/closure_capture_warning_spec.spl`

**Current:** 33 lines, 3 placeholder tests
**Target:** 150+ lines, 15+ real tests

**Tests to add:**
```simple
describe "Closure Capture Detection":
    it "detects simple outer var modification":
        code = "var x = 0\nfn f(): x = 1"
        warnings = analyze(code)
        expect(warnings.len()).to_be_greater_than(0)
        expect(warnings[0]).to_contain("x")

    it "detects compound assignment":
        code = "var count = 0\nfn inc(): count += 1"
        # Should warn

    it "detects multiple variables":
        code = "var a = 0\nvar b = 0\nfn f():\n    a = 1\n    b = 2"
        warnings = analyze(code)
        expect(warnings.len()).to_equal(4)  # 2 vars × 2 lines each

    it "does not warn for local variables":
        code = "fn f():\n    var x = 0\n    x = 1"
        warnings = analyze(code)
        expect(warnings.len()).to_equal(0)

    it "does not warn for parameters":
        code = "fn f(x: i64):\n    x = 1"
        warnings = analyze(code)
        expect(warnings.len()).to_equal(0)

    it "detects nested function modification":
        code = "var x = 0\nfn outer():\n    fn inner():\n        x = 1"
        # Should warn

    it "warns for class field access is OK":
        code = "class C:\n    x: i64\nimpl C:\n    me set(v: i64):\n        self.x = v"
        warnings = analyze(code)
        expect(warnings.len()).to_equal(0)  # self.x is OK
```

**Helper function:**
```simple
fn analyze(code: text) -> [text]:
    use core.lexer.{lex}
    use core.parser.{parse}
    use core.ast.{ast_reset}
    use core.closure_analysis.{analyze_closure_capture, closure_warnings_get}

    ast_reset()
    val tokens = lex(code)
    parse(tokens)
    analyze_closure_capture()
    closure_warnings_get()
```

**Deliverable:**
- Comprehensive test suite
- All tests passing
- Edge cases covered

---

### Agent 2: `code` agent - Closure Warning Integration
**Task:** Integrate closure analysis into compiler/test runner

**Files to modify:**
1. `src/app/test_runner_new/test_runner_main.spl`:
   - Call `analyze_closure_capture()` after parsing each test file
   - Display warnings before test results
   - Add `--no-closure-warnings` flag support

2. `src/app/cli/main.spl`:
   - Add `--Wno-closure-capture` flag
   - Store in compilation options

3. Add warning display:
```simple
fn display_closure_warnings(file_path: text):
    use core.closure_analysis.{closure_warnings_has, closure_warnings_get}

    if closure_warnings_has():
        print "⚠️  Closure warnings in {file_path}:"
        for warning in closure_warnings_get():
            print "  {warning}"
        print ""
```

**Integration point in test_runner_main.spl:**
```simple
fn run_single_test(file_path: text, ...):
    # ... existing parsing ...

    # Add closure analysis
    analyze_closure_capture()
    display_closure_warnings(file_path)

    # ... run tests ...
```

**Deliverable:**
- Warnings displayed in test runner
- CLI flag support
- Integration complete

---

### Agent 3: `code` agent - Ignored Return Warnings
**Task:** Implement ignored return value warnings in eval.spl

**File:** `src/compiler_core/interpreter/eval.spl`

**Implementation:**

1. Add warning tracking:
```simple
var eval_warnings: [text] = []

fn eval_get_warnings() -> [text]:
    eval_warnings

fn eval_reset():
    # ... existing reset ...
    eval_warnings = []

export eval_get_warnings
```

2. Track function return types:
```simple
var function_return_types: [(text, text)] = []  # (fn_name, return_type)

fn eval_function_decl(decl_idx: i64):
    val fn_name = decl_get_name(decl_idx)
    val return_type = decl_get_return_type(decl_idx)  # May need AST update

    if return_type != "" and return_type != "()":
        function_return_types.push((fn_name, return_type))

    # ... existing impl ...
```

3. Detect ignored calls:
```simple
fn eval_stmt(stmt_idx: i64, env: Env) -> Value:
    val tag = stmt_get_tag(stmt_idx)

    if tag == STMT_EXPR:
        val expr_idx = stmt_get_expr(stmt_idx)
        val expr_tag = expr_get_tag(expr_idx)

        if expr_tag == EXPR_CALL:
            # Check if function has non-void return type
            val fn_name = expr_get_str(expr_get_left(expr_idx))
            val has_return = function_has_return_type(fn_name)

            if has_return:
                val return_type = function_get_return_type(fn_name)
                val msg = "warning: return value of type '{return_type}' from function '{fn_name}' is ignored"
                eval_warnings.push(msg)

    # ... rest of eval_stmt ...
```

4. Helper functions:
```simple
fn function_has_return_type(fn_name: text) -> bool:
    for pair in function_return_types:
        if pair[0] == fn_name:
            return true
    return false

fn function_get_return_type(fn_name: text) -> text:
    for pair in function_return_types:
        if pair[0] == fn_name:
            return pair[1]
    return "unknown"
```

**Deliverable:**
- Warning system implemented
- All tests in `ignored_return_warning_spec.spl` pass
- No false positives

---

### Agent 4: `code` agent - Generic Syntax Lexer
**Task:** Update lexer to track generic context

**File:** `src/compiler_core/lexer.spl` or `src/compiler_core/lexer_struct.spl`

**Changes:**

1. Add context tracking to CoreLexer:
```simple
class CoreLexer:
    # ... existing fields ...
    last_token_was_ident: bool = false
    in_type_position: bool = false
```

2. Update `next_token()`:
```simple
fn next_token() -> Token:
    # ... existing impl ...

    # Track if last token was identifier
    if token.tag == TOKEN_IDENT:
        self.last_token_was_ident = true
    else:
        self.last_token_was_ident = false

    # Track type position context
    if token.tag == TOKEN_COLON:
        self.in_type_position = true
    elif token.tag == TOKEN_COMMA or token.tag == TOKEN_RPAREN:
        self.in_type_position = false

    return token
```

3. Disambiguate `<` token:
```simple
fn lex_less_than() -> Token:
    # If previous token was identifier and we're in type position
    # this might be a generic type parameter start
    if self.last_token_was_ident and self.in_type_position:
        # Check ahead: if we see `Ident`, `Comma`, or `Gt`, it's generic
        val next_char = peek_char(1)
        if is_alpha(next_char) or next_char == '>' or next_char == ',':
            return Token(tag: TOKEN_LT_GENERIC, value: "<")

    # Otherwise it's a comparison operator
    return Token(tag: TOKEN_LT, value: "<")
```

**Deliverable:**
- Lexer distinguishes `<` contexts
- New token type `TOKEN_LT_GENERIC`
- Tests pass

---

### Agent 5: `code` agent - Generic Syntax Parser
**Task:** Add parser support for generic type parameters/arguments

**File:** `src/compiler_core/parser.spl`

**Changes:**

1. Add AST nodes:
```simple
# In ast.spl or ast_types.spl
val DECL_TYPE_PARAM = 100  # Type parameter declaration
val TYPE_GENERIC = 101     # Generic type usage

fn decl_make_type_param(name: text) -> i64:
    # Creates type parameter AST node

fn type_make_generic(base_type: text, type_args: [i64]) -> i64:
    # Creates generic type application AST node
```

2. Parse type parameters:
```simple
fn parse_type_params() -> [i64]:
    # Parses <T, U, V>
    var params: [i64] = []

    if not check(TOKEN_LT_GENERIC):
        return params

    consume(TOKEN_LT_GENERIC, "Expected '<'")

    while true:
        val name = consume(TOKEN_IDENT, "Expected type parameter name").value
        params.push(decl_make_type_param(name))

        if not match(TOKEN_COMMA):
            break

    consume(TOKEN_GT, "Expected '>'")
    return params
```

3. Parse type arguments:
```simple
fn parse_type_with_args() -> i64:
    # Parses Box<T> or Option<Result<i64, text>>
    val base_type = consume(TOKEN_IDENT, "Expected type name").value

    if not check(TOKEN_LT_GENERIC):
        return type_make_simple(base_type)

    consume(TOKEN_LT_GENERIC, "Expected '<'")

    var type_args: [i64] = []
    while true:
        type_args.push(parse_type_with_args())  # Recursive for nested

        if not match(TOKEN_COMMA):
            break

    consume(TOKEN_GT, "Expected '>'")
    return type_make_generic(base_type, type_args)
```

4. Update class/function parsing:
```simple
fn parse_class_decl() -> i64:
    consume(TOKEN_CLASS, "Expected 'class'")
    val name = consume(TOKEN_IDENT, "Expected class name").value

    # NEW: Parse type parameters
    val type_params = parse_type_params()

    consume(TOKEN_COLON, "Expected ':'")
    # ... rest ...

    return decl_make_class(name, type_params, fields, methods)

fn parse_function_decl() -> i64:
    consume(TOKEN_FN, "Expected 'fn'")
    val name = consume(TOKEN_IDENT, "Expected function name").value

    # NEW: Parse type parameters
    val type_params = parse_type_params()

    consume(TOKEN_LPAREN, "Expected '('")
    # ... rest ...
```

**Deliverable:**
- Parser handles generic syntax
- AST stores type parameters
- All tests in `generic_syntax_spec.spl` pass (real parsing, not placeholders)

---

### Agent 6: `test` agent - Integration Testing
**Task:** Run full test suite and verify no regressions

**Tests to run:**
```bash
bin/simple test                          # All 4067+ tests
bin/simple test test/unit/compiler/     # Closure warnings
bin/simple test test/unit/compiler_core/         # Generic + ignored return
bin/simple test test/unit/parser/       # Multiline bool
bin/simple test test/unit/runtime/      # Module closures
```

**Verification:**
- ✅ All existing tests still pass (4067+)
- ✅ New tests pass:
  - closure_capture_warning_spec.spl (15+ tests)
  - ignored_return_warning_spec.spl (20+ tests)
  - generic_syntax_spec.spl (52 tests)
  - multiline_bool_spec.spl (18 tests)
  - module_closure_spec.spl (10 tests)
- ✅ No new failures
- ✅ Performance acceptable (< 30 seconds total)

**Deliverable:**
- Test report confirming all pass
- Performance metrics
- Regression analysis

---

## Execution Order

### Phase 1: Parallel (Agents 1, 3, 4)
**Time:** 2-3 hours
- Agent 1: Closure warning tests
- Agent 3: Ignored return implementation
- Agent 4: Generic lexer updates

**Dependencies:** None (can run in parallel)

### Phase 2: Sequential (Agent 2, 5)
**Time:** 2-3 hours
- Agent 2: Closure warning integration (needs Agent 1 tests)
- Agent 5: Generic parser (needs Agent 4 lexer)

**Dependencies:**
- Agent 2 depends on Agent 1 (needs tests to validate)
- Agent 5 depends on Agent 4 (needs TOKEN_LT_GENERIC)

### Phase 3: Verification (Agent 6)
**Time:** 30 minutes
- Agent 6: Full test suite
- Verify all features work together
- Check for regressions

**Dependencies:** All previous agents complete

---

## Success Criteria

### Minimum Viable (MVP)
- [x] Multiline bool tests pass (18/18)
- [x] Module closure tests pass (10/10)
- [ ] Closure warnings integrated and working
- [ ] Ignored return warnings implemented
- [ ] Generic syntax parser accepts `<>` syntax

### Complete Success
- [ ] All 4067+ original tests pass
- [ ] All new tests pass (115+ new tests)
- [ ] Zero regressions
- [ ] Documentation updated
- [ ] User guide created

### Stretch Goals
- [ ] Closure analysis in compiler mode (not just interpreter)
- [ ] Generic type checking (not just parsing)
- [ ] IDE integration (LSP warning support)
- [ ] Performance optimization (< 1ms per analysis)

---

## Risk Mitigation

### Risk 1: AST API Incomplete
**Impact:** Parser can't store type parameters
**Mitigation:** Use AST extra fields or create new node types
**Fallback:** Store as string annotations, parse later

### Risk 2: Test Runner Integration Complex
**Impact:** Warnings not displayed correctly
**Mitigation:** Start with simple print, iterate
**Fallback:** CLI tool to run analysis separately

### Risk 3: Performance Degradation
**Impact:** Tests run slower
**Mitigation:** Make analysis opt-in (`--enable-warnings`)
**Fallback:** Cache analysis results

### Risk 4: False Positives
**Impact:** Too many warnings, users ignore
**Mitigation:** Thorough testing of edge cases
**Fallback:** Add `--Wno-*` flags to disable specific warnings

---

## Deliverables Summary

**Code:**
- `src/compiler_core/closure_analysis.spl` (187 lines - already done)
- `src/compiler_core/interpreter/eval.spl` (+ ~100 lines for warnings)
- `src/compiler_core/lexer.spl` (+ ~50 lines for context tracking)
- `src/compiler_core/parser.spl` (+ ~200 lines for generics)
- `src/app/test_runner_new/test_runner_main.spl` (+ ~50 lines for integration)

**Tests:**
- `test/unit/compiler/closure_capture_warning_spec.spl` (150+ lines)
- `test/unit/compiler_core/ignored_return_warning_spec.spl` (124 lines - done)
- `test/unit/compiler_core/generic_syntax_spec.spl` (191 lines - done)
- `test/unit/parser/multiline_bool_spec.spl` (143 lines - done)
- `test/unit/runtime/module_closure_spec.spl` (85 lines - done)

**Documentation:**
- `doc/report/analysis_status_2026-02-14.md` (done)
- `doc/report/implementation_plan_2026-02-14.md` (this file)
- `doc/report/module_closure_investigation_2026-02-14.md` (done)
- `doc/report/module_closure_resolution_2026-02-14.md` (done)
- Update `MEMORY.md` with new features
- Update `CLAUDE.md` with new warnings

**Total Estimated Lines:** ~1,500 lines of new/modified code + tests

---

## Timeline

**Optimistic:** 6-8 hours (all agents succeed, no blockers)
**Realistic:** 10-12 hours (some rework, debugging needed)
**Pessimistic:** 15-20 hours (major issues, design changes)

**Recommended approach:** Start with Phase 1 (3 parallel agents), evaluate results, then proceed to Phase 2.

---

## Agent Spawn Commands

```bash
# Phase 1 - Parallel
Task(test agent): "Expand closure_capture_warning_spec.spl with comprehensive tests"
Task(code agent): "Implement ignored return warnings in eval.spl"
Task(code agent): "Add generic context tracking to lexer"

# Phase 2 - Sequential (after Phase 1)
Task(code agent): "Integrate closure analysis into test runner"
Task(code agent): "Add generic syntax parsing support"

# Phase 3 - Verification
Task(test agent): "Run full test suite and verify no regressions"
```

---

**Status:** Ready for execution
**Next Step:** Spawn Phase 1 agents
