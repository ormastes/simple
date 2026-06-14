# Bug: f64 payloads zero out when flowing through deeply nested struct/enum returns

- **ID:** interp_f64_nested_struct_payload_zero_2026-06-14
- **Severity:** P1 (blocks numeric verification of the whole spreadsheet formula engine)
- **Discovered:** 2026-06-14, while hardening `src/app/office/sheets/formula.spl`
- **Status:** OPEN — **root cause REFINED 2026-06-14** (see "Refined root cause" below; the "nested struct" framing was a symptom, not the cause)

## Summary

`f64` values are **correct in simple/direct code** but collapse to `0.0` once they
flow through several levels of nested function calls that return structs/enums
carrying the `f64` (e.g. `EvalResult { value: CellValue.NumberVal(f64) }`). The
spreadsheet formula evaluator is exactly this shape, so every numeric formula —
including the **pre-existing** `SUM`, `AVERAGE`, `MIN`, `MAX` — evaluates to `0`
through the affected backends. This is a toolchain defect, not a defect in the
formula logic.

## Refined root cause (2026-06-14 — bisecting probes)

The "nested struct/enum" framing is a **symptom**, not the cause. Minimal repro:

```
fn f() -> f64:
    5.5
fn main():
    if f() > 5.0: print("direct:OK") else: print("direct:BAD")   # -> direct:OK
    val x = f()
    if x > 5.0: print("bound:OK") else: print("bound:BAD")        # -> bound:BAD
    print("x.to_i64()={x.to_i64()}")                              # -> 0
```

Bisection results (interpreter, via probes in /tmp/f64/):
- `f() > 5.0` used **directly inline** → correct.
- `val x = f(); x > 5.0` → **wrong (x is 0.0)**, regardless of `val x: f64 =` annotation.
- `val x = 5.5` (literal RHS) → correct. `val box = Box(v: 7.5); box.v` (literal stored in a struct field inside the callee, returned) → correct.
- i64 function returns bound to a local → correct. f64 **param** passthrough, explicit `return`, arithmetic, and passing the call result as an arg all break the same way once the result is **stored/passed** rather than consumed inline.
- Struct-wrap cross-check: `Box(v: x).v` of an already-bound `x` stays 0 → the stored bits are genuinely 0, not a mis-read.

**Conclusion:** the bug is **type propagation of a function-call expression whose return type is `f64`** into a binding/argument slot. When the f64 call result is consumed inline, the comparison knows it is float and reads it correctly; when it is **bound to a local (or passed into another frame)**, the slot is treated as i64, so the float return (returned in a float register / float Value) is read as an integer `0`. It is NOT interpreter value-boxing and NOT struct-nesting.

**Breadth (critical):** reproduces **identically** in all three execution paths — the seed Rust interpreter, the self-hosted interpreter, AND `native-build` (cranelift codegen). A defect common to all three lives in the **shared frontend type layer** (type-checking / HIR lowering of `Let`/argument bindings from call expressions), not in any one backend's value representation. native-build did NOT core in this minimal probe (it returned wrong values, exit 0); the earlier "core dump" was a separate/more-complex probe.

**Where to fix:** the let/argument binding must take its type from the callee's declared return type. Present in BOTH the Rust seed (confirmed via `native-build`) and the self-hosted `.spl` compiler — so a complete fix touches both frontends + a seed rebuild, with i64/text regression guards. The string-interpolation "0.0" symptom is downstream (the bound value really is 0); fixing the binding type fixes it.

## Evidence

Direct, shallow f64 works:

```
fn id(x: f64) -> f64: x        # id(3.0) > 2.5  -> true   (OK)
fn want_three() -> f64: 3.0    # want_three() > 2.5 -> true (OK)
add(2.0, 4.0).to_i64()         # -> 6  (correct value)
```

But:

- **f64 string interpolation** renders `0.0` even when the value is correct
  (`print("{id(3.0)}")` → `0.0`). Misleading for probes — branch on the value
  instead of printing it.
- **Some f64-literal comparisons misbehave**: `add(2.0,4.0) > 5.5` returned
  false though `add(2.0,4.0).to_i64()` is `6`.
- **Deeply nested return path zeros the payload**: extracting the `f64` out of
  `CellValue.NumberVal` after it traversed the recursive-descent evaluator
  yields `0.0`. `=SUM(1,2,3,4)` → `0` (pre-existing function), `=SQRT(16)` → `0`,
  every numeric formula → `0`.
- **Even shallow leaf-math is unreliable**: calling thin public wrappers over the
  leaf helpers (e.g. `office_sqrt(16.0).to_i64()`) was correct in the single
  exact-integer case (`16 → 4`), but `office_floor(2.7).to_i64()`,
  `office_ceil(2.1).to_i64()`, and `office_round(2.5,0).to_i64()` returned
  **garbage bit patterns** (e.g. `274721116585879142`) or `0` — and reusing a
  returned f64 in further arithmetic (`office_sqrt(2.0) * 100.0`) also produced
  garbage. So the math cannot be positively verified even shallowly; the new
  formula functions are "correct by construction" only.

## Per-backend behavior (probe: `evaluate_formula` over `app.office.sheets`)

| Backend | f64 formula result | Notes |
|---|---|---|
| `bin/simple run` (interpreter) | `0` | payload zeroed through nesting |
| `bin/simple <file>.smf` (compiled, interp fallback) | `0` | same |
| test runner (compiled mode) | `0` | numeric examples fail; empty-result examples pass |
| `simple native-build` (clang/native) | **core dump** (one probe) | the single probe built so far cored on its first `evaluate_formula` call; not yet isolated. See recent "native-build codegen root cause" work |

The integer-safe display path (`evaluate_formula_display_text`, pure `i64`)
works for **literal** arithmetic (`=2+3` → `5`, `=10-4` → `6`) under
`bin/simple run`, but cell-reference resolution still routes through the `f64`
`CellValue.NumberVal` and zeros (`=A2+A3` with A2=10,A3=5 → `0`), and the test
runner's compiled mode returns empty for even literal arithmetic.

## Impact

- No available backend can verify the numeric correctness of the spreadsheet
  formula engine end-to-end. Only **termination/structural** behavior (e.g.
  circular-reference depth guard returning an empty display) is verifiable in
  the test runner.
- Observed in the spreadsheet formula engine only. It *may* affect other
  numeric-heavy modules that carry `f64` through nested struct/enum returns
  (perf, ML, geometry) on the interpreter/runner path, but that is unverified
  beyond this module — do not assume broad impact without reproducing.

## Repro

1. Define `fn want_three() -> f64: 3.0`; `print("{want_three()}")` → `0.0`,
   but `if want_three() > 2.5: print("OK")` → `OK`.
2. `evaluate_formula("=SUM(1,2,3,4)", sheet)` then extract the `NumberVal` →
   `0` under `bin/simple run`.
3. `simple native-build --entry <probe>.spl` then run the binary → core dump on
   the first `evaluate_formula` call.

## Proposed investigation

- Inspect interpreter value boxing/unboxing for `f64` when it is a struct field
  or enum payload returned across call frames (suspect: `Value::F64` copy vs.
  reuse, or i64/f64 tag confusion in `rt_value_*` unboxing).
- Inspect f64 string interpolation (`to_string`/format) — separate but related
  defect that makes probes misleading.
- Triage the native-build codegen crash on f64 paths alongside the existing
  "native-build codegen root cause" lane.

## Workaround in use

`src/app/office/sheets/formula.spl` keeps a parallel integer-safe display path
(`evaluate_formula_display_text`) for UI surfaces; the spec
`test/01_unit/app/office/sheets/formula_harden_spec.spl` asserts only the
termination behavior that the runner can execute.
