# SDoctest: ```simple Blocks - No Validation Mode

**Date:** 2026-02-07
**Status:** Planning
**Goal:** Change ```simple code blocks to run without exit code validation

---

## 1. Current Behavior Analysis

### 1.1 Two Block Types

The sdoctest system currently supports two fence types:

| Fence Type | Purpose | Current Behavior | Use Case |
|------------|---------|------------------|----------|
| ```sdoctest | Interactive REPL | Strips `>>>` prompts, removes output lines, checks exit code | Executable examples with expected output |
| ```simple | Regular code | Executes full code, checks exit code | Code demonstrations |

### 1.2 Current Validation

**Location:** `src/app/test_runner_new/sdoctest/runner.spl:302-313`

```simple
if exit_code == 0:
    BlockResult(
        block: block, status: BlockStatus.Passed,
        duration_ms: duration_ms, stdout: stdout, stderr: stderr, error: ""
    )
else:
    val error_msg = extract_block_error(stderr, stdout)
    BlockResult(
        block: block, status: BlockStatus.Failed,
        duration_ms: duration_ms, stdout: stdout, stderr: stderr,
        error: error_msg
    )
```

**Problem:** Both `sdoctest` and `simple` blocks fail if exit code != 0, even if they're just demonstration code.

### 1.3 Existing but Unused Infrastructure

**Location:** `src/app/test_runner_new/sdoctest/types.spl:13`

```simple
enum SdoctestModifier:
    Skip
    ShouldFail
    FailAsSuccess
    IgnoreOutput        # ← Defined but NEVER USED
    Init(text)
    Env(text)
    Tag(text)
```

The `IgnoreOutput` modifier exists and is:
- ✅ Parsed from fence modifiers (extractor.spl:143-144)
- ✅ Has accessor method `has_modifier_ignore_output()` (types.spl:109-114)
- ❌ **NEVER checked in runner.spl** - completely unused!

---

## 2. Problem Statement

### 2.1 README.md Usage Patterns

Analyzing README.md code blocks:

**```sdoctest blocks (7 instances):**
- Interactive examples with `>>>` prompts
- Expected to pass with specific output
- Current behavior: ✅ Correct

**```simple blocks (12 instances):**
- 9 blocks with `<!--sdoctest:skip-next-->` marker
- 3 blocks without skip marker (lines 240-264, 351-383, 505-528)
- **These are DEMONSTRATION CODE** - may not have `main` function, may not return 0
- Current behavior: ❌ Fails if exit code != 0

### 2.2 User Request

> "lets change feature ```simple to just run without output check"

**Interpretation:**
1. ```simple blocks should execute the code (syntax/semantic check)
2. Should NOT fail if exit code != 0
3. Should only fail on infrastructure errors (timeout, parse error, crash)
4. Output can be displayed but is not validated

**Use cases:**
- README examples showing language features
- Code snippets that don't have complete programs
- Demonstration of syntax patterns
- Exploratory code that may error intentionally

---

## 3. Design Options

### Option A: Make ```simple Always Ignore Exit Code (Recommended)

**Approach:** All ```simple blocks pass unless timeout/parse error

**Changes:**
1. Modify `runner.spl:302-313` to check block language
2. If `language == "simple"` → always pass (unless Error status)
3. If `language == "sdoctest"` → check exit code (current behavior)

**Pros:**
- Simple, intuitive behavior
- Matches user expectation: "simple blocks just run"
- No modifier syntax needed
- Clear semantic difference: `sdoctest` = verified, `simple` = demonstration

**Cons:**
- Cannot detect legitimate failures in `simple` blocks
- May hide real errors in documentation

**Code change:**
```simple
# In runner.spl, replace lines 302-313:
if exit_code == 0:
    BlockResult(
        block: block, status: BlockStatus.Passed,
        duration_ms: duration_ms, stdout: stdout, stderr: stderr, error: ""
    )
else:
    # NEW: Check if block is 'simple' fence → always pass
    if block.language == "simple":
        BlockResult(
            block: block, status: BlockStatus.Passed,
            duration_ms: duration_ms, stdout: stdout, stderr: stderr,
            error: "exit code {exit_code} (ignored for simple blocks)"
        )
    else:
        val error_msg = extract_block_error(stderr, stdout)
        BlockResult(
            block: block, status: BlockStatus.Failed,
            duration_ms: duration_ms, stdout: stdout, stderr: stderr,
            error: error_msg
        )
```

### Option B: Use IgnoreOutput Modifier (More Flexible)

**Approach:** Implement the existing `IgnoreOutput` modifier

**Usage:**
```markdown
# Always pass, even on error
```simple:ignore_output
x = undefined_var  # Would normally fail, but passes
```

# Explicitly validate
```simple
fn main() -> i64:
    0  # Must return 0 or fails
```
```

**Pros:**
- Opt-in behavior - explicit intent
- Can validate `simple` blocks when needed
- Reuses existing infrastructure

**Cons:**
- Requires fence modifier on every demonstration block
- More verbose
- User must remember to add `:ignore_output`

**Code change:**
```simple
# In runner.spl, after line 280 (after should_fail check):

# NEW: Check ignore_output modifier
val ignore_output = block.has_modifier_ignore_output()

if exit_code == 0:
    BlockResult(...)
else:
    if ignore_output:
        BlockResult(
            block: block, status: BlockStatus.Passed,
            duration_ms: duration_ms, stdout: stdout, stderr: stderr,
            error: "exit code {exit_code} (ignored)"
        )
    else:
        BlockResult(
            block: block, status: BlockStatus.Failed,
            ...
        )
```

### Option C: Hybrid Approach

**Approach:**
- ```simple blocks ignore exit code by default
- ```simple:strict to enable validation
- ```sdoctest always validates

**Modifiers:**
```markdown
# Default: no validation
```simple
demo_code()
```

# Explicit validation
```simple:strict
fn main() -> i64: 0
```

# Always validated
```sdoctest
>>> 1 + 1
2
```
```

**Pros:**
- Best of both worlds
- Backward compatible
- Explicit opt-in for validation

**Cons:**
- Adds new modifier `:strict`
- More complexity

---

## 4. Recommended Solution: Option A

**Decision: Make ```simple blocks always ignore exit code**

### 4.1 Rationale

1. **User Expectation**: "simple blocks just run" is clearest with no validation
2. **README Usage**: 75% of simple blocks already skip validation (via `<!--sdoctest:skip-next-->`)
3. **Semantic Clarity**:
   - `sdoctest` = verified executable examples
   - `simple` = demonstration code
4. **Simplicity**: No modifier syntax required
5. **Existing Pattern**: Many projects use this distinction (Rust book uses `rust,ignore` vs `rust`)

### 4.2 Validation Strategy

```simple blocks will:
- ✅ Parse the code (syntax check)
- ✅ Execute the code (semantic check)
- ✅ Detect timeouts (infrastructure error)
- ✅ Detect parse errors (fail the block)
- ✅ Detect runtime crashes (infrastructure error)
- ❌ Ignore exit code (pass even if != 0)

Error status hierarchy:
1. `Error` - Infrastructure failure (timeout, parse error, crash)
2. `Passed` - Code ran successfully OR exit code != 0 (for simple blocks)
3. `Failed` - Only for sdoctest blocks with wrong exit code
4. `Skipped` - Marked with :skip or unsupported keywords
```

---

## 5. Implementation Plan

### 5.1 Changes Required

**File: `src/app/test_runner_new/sdoctest/runner.spl`**

```diff
fn run_sdoctest_block(...) -> BlockResult:
    # ... existing code ...

    if exit_code == 0:
        BlockResult(
            block: block, status: BlockStatus.Passed,
            duration_ms: duration_ms, stdout: stdout, stderr: stderr, error: ""
        )
    else:
+       # Simple blocks ignore exit code - only check parse/timeout errors
+       if block.language == "simple":
+           BlockResult(
+               block: block, status: BlockStatus.Passed,
+               duration_ms: duration_ms, stdout: stdout, stderr: stderr,
+               error: ""  # No error - just demonstration code
+           )
+       else:
            val error_msg = extract_block_error(stderr, stdout)
            BlockResult(
                block: block, status: BlockStatus.Failed,
                duration_ms: duration_ms, stdout: stdout, stderr: stderr,
                error: error_msg
            )
```

**File: `README.md`**

Remove `<!--sdoctest:skip-next-->` markers from simple blocks:

```diff
- <!--sdoctest:skip-next-->
  ```simple
  struct Point:
      x: f64
      y: f64
  ```
```

### 5.2 Testing Strategy

**Unit Tests** (`test/app/test_runner_new/sdoctest/runner_spec.spl`):

```simple
describe "simple blocks with non-zero exit":
    it "passes even with syntax error":
        val block = SdoctestBlock(
            source_file: "test.md",
            line_number: 10,
            code: "undefined_var",
            language: "simple",
            modifiers: []
        )
        val result = run_sdoctest_block(block, config, "default", options, "")
        expect(result.status).to_equal(BlockStatus.Passed)

describe "sdoctest blocks with non-zero exit":
    it "fails with syntax error":
        val block = SdoctestBlock(
            source_file: "test.md",
            line_number: 20,
            code: "undefined_var",
            language: "sdoctest",
            modifiers: []
        )
        val result = run_sdoctest_block(block, config, "default", options, "")
        expect(result.status).to_equal(BlockStatus.Failed)
```

**Integration Test:**

Run `bin/simple test --sdoctest README.md` and verify:
- All `simple` blocks pass
- `sdoctest` blocks still validate correctly
- No false failures

### 5.3 Documentation Updates

**File: `doc/spec/testing/sdoctest.md`**

Add section:

```markdown
## Block Type Behavior

### ```simple Blocks - Demonstration Mode

Simple blocks execute code without exit code validation. They pass as long as:
- Code parses without syntax errors
- No timeout occurs
- No infrastructure crash

Use for:
- Language feature demonstrations
- Incomplete code snippets
- Exploratory examples

```simple
# This passes even though there's no main function
struct Point:
    x: f64
    y: f64
```

### ```sdoctest Blocks - Verified Examples

Sdoctest blocks are fully validated:
- Code must execute successfully (exit code 0)
- Output must match expected output
- Failures are reported as test failures

```sdoctest
>>> 1 + 1
2
>>> "hello".len()
5
```
```

**File: `README.md`**

Update "Quick Start" section:

```diff
  ### Your First Program

+ The README uses two types of code blocks:
+ - ```simple - Demonstration code (not validated)
+ - ```sdoctest - Verified examples (must pass)
+
  ```sdoctest
  # hello.spl
  >>> main = 0  # Entry point, returns exit code
  ```
```

---

## 6. Migration Path

### 6.1 README.md Cleanup

**Before (current):**
```markdown
<!--sdoctest:skip-next-->
```simple
struct Point:
    x: f64
    y: f64
```
```

**After (with this change):**
```markdown
```simple
struct Point:
    x: f64
    y: f64
```
```

**Action:** Remove 9 `<!--sdoctest:skip-next-->` markers from README.md

### 6.2 Other Documentation Files

Search all `.md` files for:
- `<!--sdoctest:skip-next-->` followed by ```simple
- Consider removing markers if they're demonstration code

```bash
# Find all skip markers
grep -r "<!--sdoctest:skip-next-->" doc/ README.md examples/
```

---

## 7. Edge Cases

### 7.1 Parse Errors

**Scenario:** ```simple block with syntax error

```simple
fn broken(
    # Missing closing paren
```

**Behavior:** Status = `Error` (parse error is infrastructure failure)

### 7.2 Runtime Crash

**Scenario:** ```simple block that panics

```simple
fn main():
    panic("crash!")
```

**Behavior:** Status = `Passed` (exit code 1 is ignored for simple blocks)

**Note:** This is acceptable - simple blocks are demonstrations, not tests

### 7.3 Timeout

**Scenario:** ```simple block with infinite loop

```simple
while true:
    pass
```

**Behavior:** Status = `Error` (timeout is infrastructure failure)

### 7.4 Explicit Validation

**Scenario:** User wants to validate a `simple` block

**Solution:** Use `sdoctest` instead:

```sdoctest
>>> fn main() -> i64:
...     0
>>> main()
0
```

Or use `:should_fail` modifier if expecting failure:

```simple:should_fail
undefined_var  # Expected to fail
```

---

## 8. Success Criteria

**Implementation Complete When:**
- ✅ ```simple blocks pass regardless of exit code
- ✅ ```sdoctest blocks still validate exit code
- ✅ README.md runs without skip markers
- ✅ All existing sdoctest tests still pass
- ✅ New unit tests verify behavior
- ✅ Documentation updated

**Metrics:**
- README.md: 0 skip markers for simple blocks (currently 9)
- Test suite: All 1597 passing tests still pass
- New tests: 4+ tests covering simple vs sdoctest behavior

---

## 9. Alternatives Considered

### 9.1 Why Not Use `:ignore_output`?

**Rejected because:**
- Requires modifier on every demonstration block
- Verbose and error-prone
- Doesn't match user mental model ("simple blocks just run")
- Would require updating all documentation

### 9.2 Why Not Just Use `:skip`?

**Rejected because:**
- `:skip` means "don't execute" - we want to execute
- Misses the benefit of syntax/parse checking
- No output in test results (skipped blocks are silent)

### 9.3 Why Not Add `:demo` Modifier?

**Rejected because:**
- Adds complexity without clear benefit
- `simple` vs `sdoctest` already provides semantic distinction
- User explicitly asked for "```simple to just run without output check"

---

## 10. Timeline

**Phase 1: Implementation (1 hour)**
- Modify `runner.spl` (20 lines)
- Add unit tests (4 tests)
- Test locally with README.md

**Phase 2: Cleanup (30 minutes)**
- Remove skip markers from README.md
- Update other documentation files

**Phase 3: Documentation (30 minutes)**
- Update `sdoctest.md` spec
- Add section to README.md

**Total:** ~2 hours

---

## 11. Open Questions

1. **Should we display exit code in output?**
   - Currently: `error: ""` (no error message)
   - Alternative: `error: "exit code 1 (ignored)"` for debugging
   - **Decision:** Show nothing - simple blocks are demonstrations

2. **Should we keep `:ignore_output` modifier?**
   - Currently: Defined but unused
   - Option A: Remove it (not needed with new behavior)
   - Option B: Keep it for explicit ignore on sdoctest blocks
   - **Decision:** Keep for backward compatibility, document as "force ignore for sdoctest blocks"

3. **Should we add `:strict` modifier for simple blocks?**
   - Allows validation of simple blocks when needed
   - Adds complexity
   - **Decision:** No - use sdoctest instead

---

## 12. Related Work

**Similar systems:**
- **Rust rustdoc:** Uses `rust,ignore` for demonstration code
- **Python doctest:** Uses `# doctest: +SKIP` for non-validated examples
- **Haskell doctest:** All examples are validated by default
- **Elixir ExDoc:** Uses `iex>` prompts for validated examples

**Our approach most similar to:** Rust's `rust` vs `rust,ignore` distinction

---

## Summary

**Change:** ```simple blocks execute without exit code validation

**Rationale:** Demonstration code doesn't need to be valid programs

**Impact:**
- README.md: Remove 9 skip markers
- Test suite: All existing tests still pass
- User experience: Clearer semantic distinction between demo and verified code

**Implementation:** 10-line change to runner.spl + tests + docs

**Next Steps:** Review and approve plan, then implement
