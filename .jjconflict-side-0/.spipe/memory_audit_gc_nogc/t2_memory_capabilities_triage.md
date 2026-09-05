# Memory Capabilities Spec — Failure Triage

**Spec file:** `test/00_formal_verification/compiler/memory_capabilities_spec.spl`
**Source under test:** `src/compiler_rust/lib/std/src/verification/models/memory_capabilities.spl`
**Run date:** 2026-06-11
**Baseline:** 4 passed / 2 failed / 6 total

---

## Failure A — "builds Lean syntax" (context: CapType, line 17–20)

### Root cause

`CapType.to_lean()` (source line 223) is:

```
val cap_lean = self.cap.to_lean_name()
"CapType.mk \"{self.type_name}\" RefCapability.{cap_lean}"
```

The call `self.cap.to_lean_name()` dispatches a method on `self.cap`, which is an
enum value (`RefCapability`) stored as a struct field of `CapType`. In the
interpreter, calling any method on an enum value extracted from a struct field
causes the `it` block to crash (the test runner reports the block as failed with
0 assertion errors, but the crash terminates the block mid-execution before any
`expect()` runs).

**Reproduction minimal:**
```spl
use verification.models.memory_capabilities as caps

describe "X":
    it "enum field method call crashes":
        val x = caps.CapType.imm_type("Int")
        val c = x.cap          # ok — field access passes
        val am = c.allows_mutation()  # CRASH — method on enum from struct field
        expect(true).to_equal(true)  # never reached
```

- `val c = x.cap` alone: PASSES
- `c.allows_mutation()` after: CRASHES

**Classification: PRODUCT BUG**
The interpreter mishandles method dispatch on enum values retrieved from
class/struct fields. The `\"` escape inside string interpolation is NOT the
cause — standalone probe confirmed that works correctly. The spec assertion is
correct and tests real desired behavior.

**Action: No spec change.** Test left failing. Bug should be filed against the
interpreter's enum-field method dispatch path.

---

## Failure B — "stores and consumes references" (context: RefEnv, lines 23–29)

### Root cause (two layers)

**Layer 1 — Value-copy semantics (SPEC BUG in the source implementation):**
`RefEnv.consume()` is a `me` method that calls `self.refs.get(name)` to obtain
a `Reference`. `Dict.get()` returns a **value copy**. The code then calls
`ref.consume()` on that copy, setting `is_consumed = true` on the copy — the
dict entry is never updated. So `is_available("x")` remains `true` after
`consume("x")` returns.

This is the documented value-semantics pattern (repo memory: "Arrays are value
types"; "cross-module mutation loss"). The fix in the *source* is to write back:
```spl
me consume(name: text) -> Result<Nil, text>:
    match self.refs.get(name):
        case Some(ref):
            if ref.is_consumed:
                Err("Reference '{name}' already consumed")
            else:
                ref.consume()
                self.refs[name] = ref   # write back mutated copy
                Ok(nil)
        case None:
            Err("Reference '{name}' not found")
```
This is a bug in `memory_capabilities.spl`, not in the spec.

**Layer 2 — Interpreter SIGSEGV on Dict.get match with class values (PRODUCT BUG):**
Even before the value-copy issue matters, the interpreter segfaults when
`match d.get(key)` is used where the dict value type is a class instance.

**Reproduction minimal:**
```spl
class Ref:
    is_consumed: bool
    fn new() -> Ref: Ref(is_consumed: false)

fn main():
    var d: Dict<text, Ref> = {}
    d["x"] = Ref.new()
    match d.get("x"):   # SIGSEGV here
        case Some(ref): print("{ref.is_consumed}")
        case None: print("none")
```
Exit code 139 (SIGSEGV). `d.get("x")` as a plain `val` without pattern-match
does not crash.

**Classification:**
- Source `RefEnv.consume()` bug: **SPEC BUG** (the source under test has wrong
  implementation — should write back the mutated copy per value-semantics).
- Interpreter SIGSEGV on `match dict.get(...)` with class values: **PRODUCT BUG**.

**Action:**
- The spec assertion (`env.is_available("x")` → `false` after `consume`) is
  **correct** — it tests the intended contract. The spec is NOT changed.
- The source implementation `RefEnv.consume()` needs the write-back fix (see
  above). However, even with that fix applied, the interpreter SIGSEGV on
  `match self.refs.get(name)` means the test will still fail at runtime.
- Test left failing. Two bugs to file:
  1. `memory_capabilities.spl` `RefEnv.consume()`: dict get/mutate/no-writeback
  2. Interpreter SIGSEGV: `match dict.get(key)` where value type is a class

---

## Summary

| # | Test | Classification | Spec changed? | Status |
|---|------|----------------|---------------|--------|
| A | "builds Lean syntax" | PRODUCT BUG (interpreter: enum-field method dispatch crash) | No | Still failing |
| B | "stores and consumes references" | PRODUCT BUG (interpreter SIGSEGV on class-valued dict match) + SOURCE BUG (no write-back in `RefEnv.consume`) | No | Still failing |

**Final count: 4 passed / 2 failed (unchanged — both failures are product bugs, no spec cover-ups applied)**
