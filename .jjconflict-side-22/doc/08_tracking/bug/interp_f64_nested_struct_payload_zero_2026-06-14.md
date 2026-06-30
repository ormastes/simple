# Bug: f64 payloads zero out when flowing through deeply nested struct/enum returns

- **ID:** interp_f64_nested_struct_payload_zero_2026-06-14
- **Severity:** P1 (blocks numeric verification of the whole spreadsheet formula engine)
- **Discovered:** 2026-06-14, while hardening `src/app/office/sheets/formula.spl`
- **Status:** OPEN — **root cause CORRECTED 2026-06-16** (see "Corrected root cause (2026-06-16)" below). The 2026-06-14 "shared frontend type layer / let-binding type from callee return type" conclusion is **REFUTED**: the emitted MIR is byte-identical between the correct Rust seed and the buggy self-hosted stage4, so the frontend is NOT at fault. The defect is in stage4's **post-MIR execution** (the self-hosted tree-walking interpreter) and, separately, its **native codegen**.

## Corrected root cause (2026-06-16 — differential bisection vs the Rust seed oracle)

Re-bisected with the Rust seed as a **confirmed-correct oracle** (`bin/release/x86_64-unknown-linux-gnu/simple_seed run` gives the right answer on every probe below; `bin/release/simple` stage4 gives the wrong one).

**Executor identified by observation** (not source-reading): `bin/release/simple run` uses `CompileMode.Interpret` → `InterpreterBackendImpl.process_module` (the tree-walking HIR interpreter in `src/compiler/70.backend/backend/interpreter.spl` + `interpreter_calls.spl` + `env.spl`), wired in `src/compiler/80.driver/driver_types.spl:52`. (`src/compiler/95.interp/mir_interpreter.spl` is NOT the run executor — it leaves `LocalAddr` unhandled and has a truncating `f64_to_bits = v as i64`; those are separate latent issues, not this bug.)

**The MIR is identical** between seed and stage4 (`compile --emit-mir`, diff empty modulo the filename comment). So the bug is purely in stage4's execution of that MIR.

**Minimal repro** (`bin/release/simple run` → prints `BAD`; seed → `OK`):
```
fn free_ret() -> f64: 3.0
fn noop(): print("pre")
fn main():
    val f = free_ret()      # f = 3.0  (correct here)
    noop()                  # ANY intervening function call
    if f > 2.5: print("OK") else: print("BAD")   # f now reads as 0 -> BAD
```

**Discriminators (all verified empirically):** corruption requires the **trifecta** —
1. the value is a **float** (i64 return values survive an intervening call), AND
2. it is a **function-call return** (a `val f = 5.5` literal survives), AND
3. there is a **subsequent function call** before first use (`val f = free_ret(); if f>2.5` with no intervening call → OK).

An aliasing probe (`val f=free_ret(); val g=other_ret(); f`) shows `f` becomes **0**, not `g`'s value.

**T1 — the key behavioral fingerprint:** inserting a *read* of `f` (e.g. an `if f > 2.5` block) **before** `noop()` makes `f` survive the later call (`after:OK`). A copy via arithmetic (`val f2 = f + 0.0`) or a struct field (`Hold(v: f)` ) before the call does **not** protect it. Because an `if`-block read adds an extra scope push/pop, this points at the **scope/environment machinery** (`env.spl`, incl. the D-9 `scope_pool` recycling) being sensitive to the exact push/pop sequence around a float call-return binding — i.e. a value-lifetime/aliasing bug in how a float `Value` from a call is held in the environment across a subsequent call, NOT register clobbering (the value lives in an env `Dict`, not a register).

**Also reproduces in `bin/release/simple native-build`** → the self-hosted native codegen has a parallel f64-call-return defect (classic "f64 return read from the integer return slot" ABI shape). Seed paths are clean. So a full fix is two-front: (a) the tree-walking interpreter's call-return/env value handling, (b) stage4 codegen's f64-return ABI. Both are pure-Simple (`src/compiler/...`) → `--pure-simple` rebuild, verified against the seed oracle. **Next step:** instrument `env.define/lookup` + `call_hir_function`'s return path, `--pure-simple` rebuild, and trace the float `Value` across the intervening call to pin the exact line.

## VERIFICATION BLOCKER (2026-06-16) — LIM-010 self-host build is broken

Attempting to fix-and-verify hit a hard infrastructure wall; **the fix cannot currently be verified in this repo state**:

1. **No working instrumented stage4.** `scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple` completes but stage3 self-host fails (LIM-010: LLVM symbol conflicts) → stage4 falls back to seed-native-build, which **stubs 535 unresolved symbols, including `backend__backend__interpreter__ParserModule` and `backend__backend__env__ParserModule`**. The resulting `build/bootstrap/full/.../simple` (16.6 MB) is a **silent no-op** (`-c "print(1+1)"` prints nothing). The only *working* self-hosted binary, `bin/release/.../simple` (461 MB), was built **2026-06-15** and predates the current tree — its recipe is not reproducible by `--pure-simple` today. So an instrumented or fixed interpreter cannot be built into a runnable CLI.
2. **Seed-driving the `.spl` interpreter is not cleanly observable.** Running `interpret_file(...)` (which drives `InterpreterBackendImpl`) under the correct Rust seed via `test/03_system/compiler/compiler_interpret_pipeline_spec.spl` works for simple programs, but: guest `print` stdout is captured/hidden by the runner; guest `extern` calls (e.g. `rt_file_write_text`) are **not bridged** by the tree-walking interpreter (no file channel out); `/tmp`-located specs fail `compiler.*` import resolution; each run is ~48 s. A float-returning guest made the probe `it` fail `is_success()`, but the failure detail was not surfaceable, so logic-vs-codegen could **not** be cleanly confirmed this way.

**Consequence:** a real fix requires first resolving **LIM-010** (stage3 self-host / LLVM symbol conflicts) so a working self-hosted compiler can be built and the fix differential-verified against the seed oracle — OR building a seed-runnable harness that exposes the `InterpreterBackendImpl` computed value (not just `is_success()`) for a float-return-survives-call case. Per the no-coverup rule, **no interpreter/codegen edit was landed**, since it could not be verified. The corrected diagnosis above stands as the durable deliverable.

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
