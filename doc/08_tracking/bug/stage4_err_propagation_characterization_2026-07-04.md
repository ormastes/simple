# Stage4 Iteration 20 Error Propagation Characterization (#95)

## RETIRED 2026-08-17 — every claim below is either FIXED in current source or already tracked elsewhere

**Binary used for the re-check:** `bin/simple` ->
`bin/release/x86_64-unknown-linux-gnu/simple`, the **Rust seed** (mtime
2026-08-16 22:59, 59,536,728 bytes). Probes run with an explicit
`SIMPLE_EXECUTION_MODE`, comparing `interpreter` vs `jit` in subprocesses
(the spec DSL provably cannot reach this lowering — see the header of
`test/01_unit/try_operator_error_propagation_spec.spl`).

Row-by-row against the tables above:

| original claim | 2026-08-17 result |
|---|---|
| Repro 1 — `Ok(42)?` yields `5` / garbage | **FIXED.** Prints `42` under both `interpreter` and `jit`. |
| Repro 2 — `?` does not propagate `Err` | **FIXED.** A marker placed after `get_err()?` never runs; `main` observes `Err("failed")` with the original payload, both engines. |
| Repro 4 — `?` does not propagate `nil` | **STILL BROKEN under `jit` only** (interpreter short-circuits correctly). This is not a stage4 artifact and is already filed with full root cause: `try_operator_on_option_no_early_return_2026-08-08.md` (OPEN, owned there). Not re-filed here. |
| Repro 5 — `??` broken | **NOT A DEFECT.** Already corrected by the 2026-07-04 coordinator note below; re-confirmed (`nil ?? "default"` -> `default`). |
| all `stage4_it20f` rows (crash / RC=132 / silent match) | **UNREPRODUCIBLE BY CONSTRUCTION.** The binary was a `/tmp` scratchpad build that no longer exists. Nothing in this doc can be re-tested against it, and the deployed-side claims it was contrasted with are fixed. |

**Proving symbols in CURRENT source** (classification is by content, not SHA):
`lower_try` in `src/compiler_rust/compiler/src/hir/lower/expr/control.rs`
now emits `LetIn tmp = <inner> in if rt_enum_check_discriminant(tmp,
disc("Err")): return tmp else: rt_enum_payload(tmp)` — a real discriminant
test plus early return, replacing the bare `rt_enum_payload(expr)` that
caused Repros 1 and 2. The same function has a `result_like_payload_type`
is-none branch handling flat-nullable scalars.

**No new specs added, deliberately.** The `Result` half already has both a
surface spec (`test/01_unit/try_operator_error_propagation_spec.spl`, whose
own header documents that it does NOT discriminate the lowering) and the
real engine-crossing guard `scripts/check/check-try-operator-error-propagation.shs`,
which was run for this retirement:

```
PASS — 3 engine(s) checked: default,interpret,jit — `?` early-returns Err with the original payload
```

The `Option` half's guard belongs with its own OPEN row, not here.

**Date:** 2026-07-04  
**Binary tested:** `/tmp/claude-1000/...scratchpad/stage4_it20f` (42M, ELF x86-64)  
**Task:** Determine whether the `?` operator's Err-propagation misbehaves on stage4-built binaries

## Executive Summary

Both the **deployed baseline** and **stage4_it20f** binaries exhibit critical errors in error/nil propagation:

- **Deployed binary**: `?` operator does NOT propagate Err or nil — silently executes continuation code instead of early-returning
- **Stage4_it20f binary**: Crashes with "field access on nil receiver" + "Illegal instruction" (RC=132) on any `?` or `??` involving nil/Err

The stage4 binary is **unsuitable for deployment** due to runtime crashes on fundamental error handling.

---

## Test Repros & Results

### Repro 1: Result Ok Path with `?`

**File:** `repro_01_simple_ok.spl`
```simple
fn get_value() -> Result<i64, text>:
    Ok(42)

fn main():
    val result = get_value()?
    print result
```

**Expected:** Print `42`

| Binary | Output | RC | Status |
|--------|--------|----|----|
| Deployed | `5` | 0 | WRONG - stub interpreter, not compiled |
| Stage4_it20f | `runtime error: field access on nil receiver` (crash) | 132 | BROKEN - crashes |

**Verdict:** Both binaries fail. Deployed doesn't execute the function correctly; stage4 crashes.

---

### Repro 2: Result Err Path with `?` (Error Should Propagate)

**File:** `repro_02_simple_err.spl`
```simple
fn get_value() -> Result<i64, text>:
    Err("failed")

fn main():
    val result = get_value()?
    print "no error"
```

**Expected:** Propagate Err → `main` returns error, nothing prints.  
**Actual:**

| Binary | Output | RC | Status |
|--------|--------|----|----|
| Deployed | `no error` | 0 | **SILENT NO-OP** - `?` did NOT propagate |
| Stage4_it20f | `runtime error: field access on nil receiver` (crash) | 132 | BROKEN - crashes |

**Verdict:** CRITICAL BUG - The `?` operator is broken in both binaries. Deployed ignores Err and continues; stage4 crashes.

---

### Repro 3: Option None Path with `?` (Nil Should Propagate)

**File:** `repro_04_simple_option.spl`
```simple
fn get_opt() -> i64?:
    nil

fn main():
    val x = get_opt()?
    print "got some"
```

**Expected:** Propagate nil → nothing prints.  
**Actual:**

| Binary | Output | RC | Status |
|--------|--------|----|----|
| Deployed | `got some` | 0 | **SILENT NO-OP** - `?` did NOT propagate nil |
| Stage4_it20f | `runtime error: field access on nil receiver` (crash) | 132 | BROKEN - crashes |

**Verdict:** CRITICAL BUG - Same pattern as Repro 2. `?` operator fails on nil propagation in both binaries.

---

### Repro 4: Null Coalescing `??` Operator

**File:** `repro_05_simple_coalesce.spl`
```simple
fn get_opt() -> text?:
    nil

fn main():
    val name = get_opt() ?? "default"
    print name
```

**Expected:** Print `default` (nil coalesces to default value).  
**Actual:**

| Binary | Output | RC | Status |
|--------|--------|----|----|
| Deployed | `nil` | 0 | WRONG - `??` operator not working, returns nil instead of "default" |
| Stage4_it20f | `runtime error: field access on nil receiver` (crash) | 132 | BROKEN - crashes |

**Verdict:** The `??` operator is also broken. Deployed doesn't coalesce; stage4 crashes.

---

### Repro 5: Match on Result (No `?` Operator)

**File:** `repro_06_simple_match.spl`
```simple
fn get_value() -> Result<i64, text>:
    Err("failed")

fn main():
    match get_value():
        Ok(value):
            print "ok"
        Err(e):
            print "err"
```

**Expected:** Match on Err arm → print `err`.  
**Actual:**

| Binary | Output | RC | Status |
|--------|--------|----|----|
| Deployed | `err` | 0 | OK - Match works correctly |
| Stage4_it20f | (empty, silent) | 0 | SILENT NO-OP - Match executed but no output |

**Verdict:** Match operator works on deployed. Stage4 match executes but produces no output (suggests IO issue or silent crash).

---

## Root Cause Analysis

### Deployed Binary Issues
1. **`?` operator does not propagate** — when Result is Err or Option is nil, the operator ignores the early-return semantic and continues execution
2. **`??` coalescing broken** — the null coalescing operator does not select the default value
3. **Root cause likely:** Stub interpreter or incomplete compiler lowering for error propagation

### Stage4_it20f Binary Issues
1. **Immediate crash on nil/Err handling** — "field access on nil receiver" suggests the binary is attempting to access a field on a nil receiver (likely Result/Option variant enum field access)
2. **"Illegal instruction" after crash** — indicates memory corruption, unaligned access, or genuine CPU instruction mismatch
3. **Root cause likely:** HIR lowering bug for Result/Option enum handling, or incorrect code generation for variant field access

---

## Impact

| Feature | Deployed | Stage4 | Severity |
|---------|----------|--------|----------|
| Error propagation (`?`) | BROKEN | CRASHES | CRITICAL |
| Nil propagation (`?`) | BROKEN | CRASHES | CRITICAL |
| Null coalescing (`??`) | BROKEN | CRASHES | CRITICAL |
| Pattern match (match) | OK | SILENT | HIGH |
| Function calls (non-error) | PARTIAL | CRASHES | CRITICAL |

**Recommendation:** Do NOT deploy stage4_it20f. The Err/nil propagation bugs render it unsuitable for any real workload. Deployed baseline is also broken but at least doesn't crash; however, critical error-handling paths are silently wrong.

---

## Repro Source Files

All repro files are in `/tmp/claude-1000/.../scratchpad/`:

1. **repro_01_simple_ok.spl** - Result Ok case
2. **repro_02_simple_err.spl** - Result Err case (should propagate)
3. **repro_04_simple_option.spl** - Option nil case (should propagate)
4. **repro_05_simple_coalesce.spl** - Null coalescing with ??
5. **repro_06_simple_match.spl** - Match on Result Err

All files use minimal imports and simple syntax to isolate error propagation behavior.

---

## Test Date & Artifacts

- **Date:** 2026-07-04
- **Deployed binary:** `bin/simple` (current release)
- **Stage4 binary:** Built from iteration 20 (stage4_it20f)
- **Test environment:** Linux x86-64, timeout 10s per test
- **Status:** All tests completed without timeout

## Coordinator verification (2026-07-04, Fable)

Independent minimal repros on the deployed binary CORRECT two rows above:

- `??` null-coalescing WORKS (`val x: text? = nil; x ?? "default"` → prints `default`). The row claiming `??` broken used a faulty repro.
- `?` Err-propagation CONFIRMED BROKEN, worse than characterized: with `fn get(flag) -> Result<int,text>` and `val v = get(flag)?`:
  - Ok(42) case: `v` = 5 (WRONG VALUE — not the payload)
  - Err case: does NOT short-circuit; `v` = garbage (348752240628) and execution continues
  - Repro: scratchpad qmark_check.spl. This is a silent-wrong-value correctness bug in the deployed interpreter, independent of stage4.
