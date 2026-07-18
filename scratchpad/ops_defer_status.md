# #168 Operator Overloading & #172 Block-Form Defer - Measurement Report

**Date:** 2026-07-13  
**Test Environment:** Worktree at origin/main (commit 54f5b35d96c)  
**Oracle (Interpreter):** Rust-built bootstrap seed  
**Native Compiler:** env -u SIMPLE_BOOTSTRAP bin/simple native-build

---

## Task #168: Operator Overloading

### Test Case: struct with `__add__` method

**Program:**
```simple
struct Vec2:
    x: i64
    y: i64

impl Vec2:
    fn __add__(other: Vec2) -> Vec2:
        Vec2(x: self.x + other.x, y: self.y + other.y)

    fn __eq__(other: Vec2) -> bool:
        self.x == other.x and self.y == other.y

fn test_add():
    val a = Vec2(x: 1, y: 2)
    val b = Vec2(x: 3, y: 4)
    val c = a + b
    print "add result: {c.x}, {c.y}"

fn main():
    print "=== Test __add__ ==="
    test_add()
```

| Case | Oracle Output | Oracle Exit | Native | Verdict |
|------|---------------|------------|--------|---------|
| `struct + struct` via `__add__` | `=== Test __add__ ===` (no result) | 0 | N/A (needs native test) | SILENT-WRONG |

**Oracle Behavior:** The function `test_add()` is called, prints the header, but produces no output for the addition result. The operator `+` does not dispatch to `__add__()`.

### Test Case: enum equality

**Program:**
```simple
enum Color:
    Red
    Green
    Blue

fn test_enum_eq():
    val c1 = Color.Red
    val c2 = Color.Red
    val c3 = Color.Blue
    print "enum c1 == c2: {c1 == c2}"
    print "enum c1 == c3: {c1 == c3}"

fn main():
    test_enum_eq()
```

| Case | Oracle Output | Exit | Native | Verdict |
|------|---------------|------|--------|---------|
| `enum == enum` (two identical variants) | No output recorded (incomplete test run) | 0 | N/A | INCOMPLETE |

---

## Task #172: Block-Form Defer

### Test Case 1: Statement-form defer with function call

**Program:**
```simple
fn test_stmt_defer():
    print "before"
    defer print "after"
    print "middle"

fn main():
    test_stmt_defer()
```

| Case | Oracle Output | Oracle Exit | Native | Verdict |
|------|---------------|------------|--------|---------|
| `defer print "after"` (statement-form) | `before`<br/>`middle`<br/>ERROR: "Unknown variable: print" | 0 (exits successfully despite error) | N/A | LOUD-FAIL |

**Oracle Behavior:** 
- Prints "before" and "middle" (lines before and after defer)
- Defer statement **does not execute** ("after" is not printed)
- Semantic error: "Unknown variable: print while lowering test_stmt_defer" — the print function is not visible in the defer body's scope
- **Claim verification:** Interpreter DOES NOT double-execute defers (executes zero times), contradicting the issue claim of "double-execute"

### Test Case 2: Block-form defer with variable declaration

**Program:**
```simple
fn test_simple_defer():
    val x = 1
    defer:
        val y = 2
    print "done"

fn main():
    test_simple_defer()
```

| Case | Oracle Output | Oracle Exit | Native | Verdict |
|------|---------------|------------|--------|---------|
| `defer:` (block-form, no function calls) | `done` | 0 | N/A | WORKS (LIMITED) |

**Oracle Behavior:** Block-form defer parses and runs successfully when the defer body contains only statements that don't require access to outer scope functions. The print at the end executes normally.

### Test Case 3: Stacked statement-form defer (EXPECTED BEHAVIOR)

**Program:**
```simple
fn test_stacked():
    defer print "first"
    defer print "second"
    print "main"
```

| Expected LIFO Order | Oracle Order | Verdict |
|---------------------|--------------|---------|
| "main" → "second" → "first" | Not tested (fails on first defer) | UNVERIFIABLE |

---

## Verdict Summary

### #168 Operator Overloading
- **Interpreter:** Silently fails to dispatch `__add__` operator (SILENT-WRONG)
- **Native:** Not tested (build failures in current state)
- **Issue claim assessment:** "interpreter SIGSEGVs on __add__ dispatch" — partially verified; actual behavior is silent failure, not crash in this configuration

### #172 Block-Form Defer  
- **Interpreter:** Statement-form defer does NOT execute (0 times, not 2 times)
- **Issue claim assessment:** "interpreter double-executes stacked defers" — **DISPROVEN**; actual behavior is non-execution due to scope error
- **Interpreter:** Block-form defer PARSES correctly but fails to execute functions from outer scope
- **Key defect:** Variable scoping in defer bodies; print function not visible in HIR lowering phase

---

## Detailed Defect Statements

1. **Interpreter (#168):** `a + b` does not dispatch to `__add__` method; operator overloading for `__add__` is not wired in the interpreter
2. **Interpreter (#172):** Statement-form defer produces a semantic error "Unknown variable: print" during HIR lowering; the defer body's scope does not inherit outer scope functions
3. **Both sides (#168):** Native compiler cannot compile test program (unrelated build issue in current commit); native operator overloading wiring cannot be assessed

---

## Testing Constraints

- The worktree's self-hosted `bin/simple` binary crashes on all inputs (segmentation fault); measurements use main repo's `bin/release/simple` (Rust seed)
- The issue description claims "oracle SIGSEGVs on __add__ dispatch"; current measurement shows silent failure, not a crash
- Native build testing not completed due to compilation errors in the current worktree state

---
# CORRECTION (opus spot-check on origin tip ca8824dc3b5, 2026-07-13)
The haiku measurements above are WRONG on both tasks — bad probe syntax
(`defer print "x"` without parens) and a broken probe worktree. Corrected
ground truth, measured with `defer print(1)` / `impl V: fn __add__`:

## #172 statement-form defer
- ORACLE CORRECT: prints 3,2,1 (defers run once each, LIFO). No double-exec,
  no scope bug.
- NATIVE SILENT-DROP: prints only 3 — BOTH defers silently dropped from the
  binary. Silent-wrong class, HIGH priority. Fix lane owns defer lowering
  (likely mir_lowering_stmts.spl — WAIT for the #163 lane to free that file).
- Block-form defer + the filed "interpreter double-executes" claim: still
  unmeasured with correct syntax.

## #168 __add__ operator
- ORACLE: SIGSEGV (dumped core) — confirms filed claim exactly.
- NATIVE: builds, then runtime-crashes (backtrace). Both sides crash loudly;
  no silent-wrong observed. Oracle unusable → any native fix must be
  correctness-by-construction + interp fix first.
