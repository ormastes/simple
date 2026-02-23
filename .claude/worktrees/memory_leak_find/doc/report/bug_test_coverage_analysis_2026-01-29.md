# Bug Test Coverage Analysis

**Date:** 2026-01-29
**Status:** Complete
**Analyzer:** Claude Code

## Executive Summary

Analyzed 7 open bugs (6 OPEN + 1 INVESTIGATING) plus 1 bug from bug_db.sdn. Found **significant test coverage gaps** that need addressing to prevent regressions.

### Coverage Summary

| Bug ID | Severity | Test Coverage | Status | Needs Test |
|--------|----------|---------------|--------|------------|
| #45 | High | ❌ None | OPEN | ✅ Yes - SSpec + Rust |
| #46 | Medium | ❌ None | OPEN | ✅ Yes - Rust |
| #47 | Critical | ❌ None | OPEN | ✅ Yes - Rust |
| #48 | Critical | ❌ None | OPEN | ✅ Yes - Rust |
| #49 | Medium | ❌ None | OPEN | ✅ Yes - Rust |
| #50 | Low | ✅ **HAS BUG** | OPEN | ✅ Fix + Test |
| #35 | Medium | ⚠️  Partial | INVESTIGATING | ✅ Yes - Complete |
| bug_db.sdn #1 | P1 | ✅ Has Test | OPEN | ⚠️  Verify Fix |

**Critical Finding:** 6 out of 8 bugs have NO test coverage. This creates high regression risk.

---

## Bug #45: MCP dispatch_to_simple_app Arg Offset 🔴

**Location:** `simple/bug_report.md:3050-3081`
**Severity:** High
**Status:** OPEN

### Description

`dispatch_to_simple_app` constructs args as `["simple_old", "<script_path>", ...user_args]`. The Simple app receives these via `sys_get_args()` and uses `args[1]` as the subcommand. But `args[1]` is the script file path, not the subcommand — all indices are shifted by 1.

### Reproduction

```bash
./target/debug/simple_old mcp server    # Tries to read "src/app/mcp/main.spl" as MCP file
./target/debug/simple_old mcp read x.spl  # args[1] = script path, not "read"
```

### Root Cause

`dispatch_to_simple_app` (src/rust/driver/src/main.rs:285-286):
```rust
let mut full_args = vec!["simple_old".to_string(), app_path.to_string_lossy().to_string()];
full_args.extend(args[1..].iter().cloned());
// Result: ["simple_old", "src/app/mcp/main.spl", "server"]
// App sees args[1] = file path, not "server"
```

MCP app expects (src/app/mcp/main.spl:44-50):
```simple
val args = sys_get_args()
if args.len() < 2:
    print_usage()
    sys_exit(1)
val command = args[1]  # ❌ Gets script path instead of command
```

### Test Coverage: ❌ NONE

**Existing Tests:**
- ✅ `test/lib/std/unit/tooling/command_dispatch_spec.spl` - Tests arg construction **logic** (lines 278-356) but doesn't verify what Simple apps actually receive via `sys_get_args()`
- ✅ `test/rust/system/command_dispatch_tests.rs` - Tests dispatch **routing** but doesn't verify arg values inside Simple apps

**Missing Test:**
```simple
# test/lib/std/unit/tooling/command_dispatch_arg_offset_spec.spl
describe "MCP arg offset bug":
    it "mcp server receives 'server' as args[1]":
        # Run: simple_old mcp server
        # Expected: args = ["simple_old", "server"]
        # Actual bug: args = ["simple_old", "src/app/mcp/main.spl", "server"]
        expect(verify_mcp_args("server")) == true
```

**Recommendation:** Add integration test that:
1. Launches `simple_old mcp server --debug`
2. Captures what MCP app receives in `sys_get_args()`
3. Verifies `args[1] == "server"` (not script path)

---

## Bug #46: simple_new1 Help Output Missing Newlines 🟡

**Location:** `simple/bug_report.md:3084-3106`
**Severity:** Medium
**Status:** OPEN

### Description

`simple_new1` (compiled by `simple_old --native`) outputs help text with no newlines — all text runs together on one line.

### Reproduction

```bash
make bootstrap-stage1
./target/bootstrap/simple_new1 --help
# All output on single line, no line breaks
```

### Root Cause

The compiled `print()` function in the native binary likely doesn't append `\n` or the string escape handling is broken in codegen.

### Test Coverage: ❌ NONE

**Existing Tests:**
- ⚠️  `test/rust/system/cli_tests.rs:37-46` - Tests Rust runtime help (not native binary)
- ⚠️  `test/lib/std/unit/cli_spec.spl:153-167` - Tests CLI library logic (not format)
- ⚠️  `test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl` - Tests codegen but not `print()` formatting

**Missing Test:**
```rust
// test/rust/system/bootstrap_help_tests.rs
#[test]
fn test_simple_new1_help_has_newlines() {
    let output = Command::new("target/bootstrap/simple_new1")
        .arg("--help")
        .output()
        .expect("Failed to run simple_new1");
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should have multiple lines
    assert!(stdout.lines().count() > 5, "Help should have multiple lines");
    assert!(stdout.contains("\n"), "Help should contain newlines");
    assert!(!stdout.starts_with("Usage:Options:"), "Lines should be separated");
}
```

**Recommendation:** Add Rust test that verifies `simple_new1 --help` output format after bootstrap.

---

## Bug #47: simple_new1 Segfault in Interpreter Mode 🔴

**Location:** `simple/bug_report.md:3109-3133`
**Severity:** Critical
**Status:** OPEN

### Description

Running `simple_new1` in interpreter mode (`-i`, default) segfaults during HIR lowering. Also shows `Runtime error: Function 'map' not found` during parsing.

### Reproduction

```bash
echo 'fn main():
    print("Hello")
' > /tmp/test.spl
./target/bootstrap/simple_new1 /tmp/test.spl
# Segmentation fault (core dumped)
```

### Root Cause

Parsing completes but HIR lowering triggers the crash. The `map` function not found error suggests stdlib functions aren't being linked properly in the self-hosted interpreter.

### Test Coverage: ❌ NONE

**Existing Tests:**
- ⚠️  `test/lib/std/system/bugs/interpreter_bugs_spec.spl` - Tests fixed interpreter bugs (BDD scoping, mutable variables) but not bootstrap crashes
- ⚠️  `simple/std_lib/test/features/bootstrap_spec.spl` - Gherkin BDD spec (NOT executable tests)

**Missing Test:**
```rust
// test/rust/system/bootstrap_interpreter_tests.rs
#[test]
fn test_simple_new1_interpreter_mode_hello_world() {
    let temp_file = "/tmp/bootstrap_test_hello.spl";
    std::fs::write(temp_file, r#"
fn main():
    print("Hello from bootstrap")
"#).unwrap();

    let output = Command::new("target/bootstrap/simple_new1")
        .arg(temp_file)  // Default is interpreter mode
        .output()
        .expect("Failed to run simple_new1");

    assert!(output.status.success(), "Should not segfault");
    assert!(!output.stderr.to_str().unwrap().contains("Segmentation fault"));
    assert!(output.stdout.to_str().unwrap().contains("Hello from bootstrap"));
}
```

**Recommendation:** Add Rust test that runs `simple_new1` in interpreter mode with simple script.

---

## Bug #48: Bootstrap Stage 2 MIR Lowering Produces 0 Modules 🔴

**Location:** `simple/bug_report.md:3136-3157`
**Severity:** Critical
**Status:** OPEN

### Description

When `simple_new1` compiles itself (`-c -o simple_new2 simple/compiler/main.spl`), the MIR lowering step produces 0 modules from 1 HIR module, causing linking to fail.

### Reproduction

```bash
./target/bootstrap/simple_new1 -c -o simple_new2 simple/compiler/main.spl
# Output: [mir] result: 0 modules, 0 errors
# Error: Codegen error: Linking failed: No object files to link
```

### Root Cause

HIR lowering and method resolution succeed. The MIR lowering silently drops all modules without reporting errors — likely a missing case or incorrect module passing between phases.

### Test Coverage: ❌ NONE

**Existing Tests:**
- ⚠️  `simple/std_lib/test/features/bootstrap_spec.spl:129-154` - Has scenarios for "MIR lowering succeeds for compiler" but these are **Gherkin BDD placeholders**, not executable tests
- ⚠️  `test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl` - Tests MIR codegen but only for simple values, not full module compilation
- ⚠️  `test/rust/integration/compiler_integration2.rs:17-29` - Tests HirModule lowering but doesn't validate MIR module counts

**Missing Test:**
```rust
// test/rust/system/bootstrap_stage2_tests.rs
#[test]
fn test_simple_new1_compiles_itself_to_stage2() {
    let output = Command::new("target/bootstrap/simple_new1")
        .args(&["-c", "-o", "target/bootstrap/simple_new2", "simple/compiler/main.spl"])
        .output()
        .expect("Failed to run simple_new1 stage 2 compile");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Should produce at least 1 MIR module
    assert!(!stderr.contains("0 modules"), "MIR lowering should produce ≥1 modules");
    assert!(output.status.success(), "Stage 2 compilation should succeed");

    // Verify binary exists
    assert!(std::path::Path::new("target/bootstrap/simple_new2").exists());

    // Verify binary works
    let test_output = Command::new("target/bootstrap/simple_new2")
        .arg("--help")
        .output()
        .expect("Failed to run simple_new2");
    assert!(test_output.status.success(), "simple_new2 should execute");
}
```

**Recommendation:** Add Rust test that verifies full bootstrap stage 2 compilation.

---

## Bug #49: Rust MCP Backend Returns Empty Text 🟡

**Location:** `simple/bug_report.md:3161-3178`
**Severity:** Medium
**Status:** OPEN

### Description

The Rust-native MCP backend (`SIMPLE_MCP_RUST=1`) returns `{"text": ""}` for valid Simple source files.

### Reproduction

```bash
SIMPLE_MCP_RUST=1 ./target/debug/simple_old mcp src/app/mcp/main.spl
# Output: {"text": ""}
```

### Test Coverage: ❌ NONE

**Existing Tests:**
- ⚠️  `test/lib/std/unit/mcp/mcp_e2e_spec.spl` - Tests MCP Simple app, not Rust backend
- ⚠️  `test/rust/system/command_dispatch_tests.rs:346-350` - Tests MCP dispatch but doesn't verify output

**Missing Test:**
```rust
// test/rust/system/mcp_backend_tests.rs
#[test]
fn test_rust_mcp_backend_returns_non_empty_text() {
    let output = Command::new("target/debug/simple_old")
        .env("SIMPLE_MCP_RUST", "1")
        .args(&["mcp", "src/app/mcp/main.spl"])
        .output()
        .expect("Failed to run Rust MCP backend");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should return JSON with non-empty text field
    assert!(stdout.contains(r#""text":"#), "Should have text field");
    assert!(!stdout.contains(r#""text":"""#), "Text field should not be empty");

    // Verify JSON structure
    let json: serde_json::Value = serde_json::from_str(&stdout)
        .expect("Output should be valid JSON");
    let text = json["text"].as_str().unwrap();
    assert!(!text.is_empty(), "MCP text should contain file content");
}
```

**Recommendation:** Add Rust test that verifies Rust MCP backend output.

---

## Bug #50: MCP dependencies_spec.spl Parse Error ✅ 🔴

**Location:** `simple/bug_report.md:3181-3197`
**Severity:** Low
**Status:** OPEN (HAS REPRODUCIBLE BUG IN TEST FILE)

### Description

The MCP dependencies test file fails with parse error: "expected expression, found Colon".

### Reproduction

```bash
./target/debug/simple_old test test/lib/std/unit/mcp/dependencies_spec.spl
# FAIL: 0 passed, 1 failed
```

### Root Cause

**FOUND THE BUG!** The test file uses incorrect syntax:

`test/lib/std/unit/mcp/dependencies_spec.spl:13-14`:
```simple
describe "Simple dependency extraction":
    """
    Simple module dependency extraction and analysis
    """
```

The description block uses `:` after `describe` when it should use parentheses or the triple-quoted string should come BEFORE the `:`.

**Correct syntax options:**
```simple
# Option 1: String argument with parentheses
describe("Simple dependency extraction"):
    it "test 1":
        # ...

# Option 2: Block docstring before colon (current usage elsewhere)
describe "Simple dependency extraction":
    it "test 1":
        # ...
```

### Test Coverage: ✅ HAS TEST (but test itself has bug)

**Existing Test:** `test/lib/std/unit/mcp/dependencies_spec.spl` - This IS the test, but it has syntax error

**Fix Required:**
```simple
# Fix line 13-14 in test/lib/std/unit/mcp/dependencies_spec.spl
describe "Simple dependency extraction":  # Remove docstring here
    it "tracks symbol usage across import styles":
        # ... existing test code
```

**Recommendation:** Fix syntax error in test file, then verify test passes.

---

## Bug #35: Test Harness Module Resolution ⚠️

**Location:** `simple/bug_report.md:35` (listed in summary, no detail section found)
**Severity:** Medium
**Status:** INVESTIGATING

### Test Coverage: ⚠️  UNKNOWN (No bug details found to assess)

**Issue:** The bug report summary lists this bug but there's no corresponding detail section in the bug report file.

**Recommendation:**
1. Document full bug details in bug report
2. Add reproduction steps
3. Add test once bug is fully specified

---

## Bug #1 (bug_db.sdn): Test Context Performance O(n²) ✅

**Location:** `doc/bug/bug_db.sdn:5`
**Severity:** P1
**Status:** OPEN

### Description

Test execution time grows exponentially with number of context blocks. 4 contexts=9.6s, 6 contexts=11.6s, 7 contexts=15.8s, 8 contexts=23.6s. Tests with 10+ contexts timeout (>120s).

### Test Coverage: ✅ HAS REPRODUCING TEST

**Reproducible Test:** `src/lib/std/src/spec/` (referenced in bug_db.sdn)

**Note:** This bug has proper test tracking via `reproducible_by` field in bug_db.sdn.

**Recommendation:** Verify the test demonstrates the performance issue and add timing assertions.

---

## Recommendations

### Priority 1: Critical Bugs (Immediate Action)

1. **Bug #47 (Segfault)** - Add test, fix crash
   - File: `test/rust/system/bootstrap_interpreter_tests.rs`
   - Test: `test_simple_new1_interpreter_mode_hello_world()`

2. **Bug #48 (0 modules)** - Add test, fix MIR lowering
   - File: `test/rust/system/bootstrap_stage2_tests.rs`
   - Test: `test_simple_new1_compiles_itself_to_stage2()`

3. **Bug #50 (Parse error)** - Fix test file syntax (1-line fix)
   - File: `test/lib/std/unit/mcp/dependencies_spec.spl:13-14`
   - Action: Remove inline docstring after `describe`

### Priority 2: High/Medium Bugs

4. **Bug #45 (Arg offset)** - Add integration test
   - File: `test/lib/std/unit/tooling/command_dispatch_arg_offset_spec.spl`
   - Test: Verify `sys_get_args()` receives correct values

5. **Bug #46 (Help newlines)** - Add bootstrap help test
   - File: `test/rust/system/bootstrap_help_tests.rs`
   - Test: `test_simple_new1_help_has_newlines()`

6. **Bug #49 (Empty text)** - Add Rust MCP backend test
   - File: `test/rust/system/mcp_backend_tests.rs`
   - Test: `test_rust_mcp_backend_returns_non_empty_text()`

### Priority 3: Documentation

7. **Bug #35** - Add full bug details to bug report
8. **Bug #1** - Verify existing test demonstrates performance issue

---

## Cross-Language Test Coverage Analysis

| Bug Type | Affects Rust | Affects Simple | Needs Rust Test | Needs Simple Test |
|----------|--------------|----------------|-----------------|-------------------|
| Arg offset (#45) | ✅ dispatch logic | ✅ app receives args | ✅ Integration | ✅ SSpec verify |
| Help newlines (#46) | ✅ codegen | ❌ N/A | ✅ Bootstrap | ❌ N/A |
| Segfault (#47) | ✅ interpreter | ✅ stdlib linking | ✅ Integration | ❌ N/A |
| 0 modules (#48) | ✅ MIR lowering | ✅ compiler code | ✅ Integration | ❌ N/A |
| Empty text (#49) | ✅ MCP backend | ❌ N/A | ✅ Unit test | ❌ N/A |
| Parse error (#50) | ❌ N/A | ✅ Test file syntax | ❌ N/A | ✅ Fix file |
| Module resolution (#35) | ⚠️  TBD | ⚠️  TBD | ⚠️  TBD | ⚠️  TBD |
| Performance (#1) | ❌ N/A | ✅ Context blocks | ❌ N/A | ✅ Has test |

**Key Insight:** Most bugs (5/7) affect Rust code and require Rust integration tests. Only 2 bugs are Simple-only.

---

## Test File Locations

### Existing Test Files (Referenced)

**Simple Tests:**
- `test/lib/std/unit/tooling/command_dispatch_spec.spl` - Dispatch logic tests
- `test/lib/std/unit/mcp/dependencies_spec.spl` - MCP dependencies (HAS BUG)
- `test/lib/std/unit/mcp/mcp_e2e_spec.spl` - MCP E2E tests
- `test/lib/std/system/bugs/interpreter_bugs_spec.spl` - Interpreter regression tests
- `simple/std_lib/test/features/bootstrap_spec.spl` - Bootstrap spec (Gherkin, not executable)

**Rust Tests:**
- `test/rust/system/command_dispatch_tests.rs` - Dispatch integration tests
- `test/rust/system/cli_tests.rs` - CLI help tests (Rust runtime only)
- `test/rust/integration/compiler_integration2.rs` - Compiler integration
- `test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl` - Codegen parity

### New Test Files Needed

**Rust:**
1. `test/rust/system/bootstrap_help_tests.rs` - For bug #46
2. `test/rust/system/bootstrap_interpreter_tests.rs` - For bug #47
3. `test/rust/system/bootstrap_stage2_tests.rs` - For bug #48
4. `test/rust/system/mcp_backend_tests.rs` - For bug #49

**Simple:**
1. `test/lib/std/unit/tooling/command_dispatch_arg_offset_spec.spl` - For bug #45

---

## Summary Statistics

- **Total Open Bugs:** 8 (7 from bug_report.md + 1 from bug_db.sdn)
- **Bugs with Test Coverage:** 2 (25%)
  - Bug #50: Has test file (but test has syntax bug)
  - Bug #1: Has reproducible test
- **Bugs without Test Coverage:** 6 (75%)
  - Bug #45, #46, #47, #48, #49, #35
- **Critical Bugs without Tests:** 2 (Bug #47, #48)
- **High Priority Bugs without Tests:** 1 (Bug #45)

**Regression Risk:** 🔴 **HIGH** - 75% of open bugs have no test coverage

**Recommended Action:** Create tests for all 6 bugs without coverage before fixing bugs to prevent future regressions.

---

**Generated by:** Claude Code
**Analysis Date:** 2026-01-29
**Source Files:**
- `/home/ormastes/dev/pub/simple/simple/bug_report.md`
- `/home/ormastes/dev/pub/simple/doc/bug/bug_db.sdn`
- Test files in `/home/ormastes/dev/pub/simple/test/`
