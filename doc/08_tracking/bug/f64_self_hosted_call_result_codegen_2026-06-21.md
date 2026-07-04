# f64 call-result corrupted in self-hosted (production) codegen

- **Status:** OPEN (seed fixed & landed; self-hosted port blocked by bootstrap breakage)
- **Severity:** High — any f64 returned from a non-inlined function is wrong in `bin/simple` compiled/JIT mode
- **Date:** 2026-06-21
- **Component:** `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` (self-hosted cranelift codegen)
- **Related (FIXED, Rust seed):** `07d87555f0e` + native print `a4b28f448c3`; see memory `project_f64_call_result_as_arg_2026-06-21`

## Symptom

`bin/simple run` (JIT) of an f64 function-call result is corrupted; the
interpreter (`SIMPLE_EXECUTION_MODE=interpret`) is correct.

```
fn half() -> f64: return 21.5
fn main(): print(half())          # interpret: 21.5   JIT: 0.0
           print(half() + half()) # interpret: 43     JIT: garbage
```

Affected forms: f64 call result printed, passed as a fn argument, fed into a
binop, or bound to a local then used. Reproduces on the deployed `bin/simple`.

## Root cause (to confirm)

The Rust seed had two coupled defects — return terminator value-converting an
f64 return (`fcvt_to_sint`) instead of bit-reinterpreting, plus unstamped
`MirInst::Call` f64 results. **The self-hosted adapter is architecturally
different** (sets the real `CL_TYPE_F64` return signature at line ~213; binop
dispatches float-ness from MIR types via `operand_is_float`), so the seed fix
does **not** transplant directly. The self-hosted root cause must be diagnosed on
its own terms — likely call-result value/type tracking in `translate_call`
(line ~757; the named-call branch does not appear to capture/stamp the result
type) and/or operand-type resolution for call destinations.

## Why not fixed here (blocker)

A fix cannot currently be **validated or deployed**:
- Stage 3 self-host fails (LIM-010 LLVM symbol conflicts) — `bootstrap-from-scratch.sh`
  falls back to the seed for stage 4.
- The freshly-bootstrapped stage4 **coredumps on trivial programs**
  (`print(1+1)`), so there is no working build→run loop to validate a
  self-hosted codegen change.
See `doc/09_report/bootstrap_crash_report_2026_04_01.md` and memory
`project_bootstrap_stage3_selfhost_broken_2026-06-17`.

Shipping an unvalidated codegen change to the production compiler is unsafe, so
the port is deferred until the bootstrap/stage4 path produces a runnable binary.

## Regression guards in place

- **Seed (validated, green):** `src/compiler_rust/compiler/src/codegen/jit_tests.rs`
  → `test_jit_f64_call_result_value` / `test_jit_f64_call_result_print`.
- **Production (pending):** `scripts/check/check-f64-call-abi.shs` runs against
  `bin/simple`; reports PENDING now and flips to PASS automatically once a
  working self-hosted build with the port is deployed.

## Fix checklist

1. Unblock the build→run loop (working stage4, or a self-host build that runs).
2. Diagnose the self-hosted call-result f64 path in `cranelift_codegen_adapter.spl`.
3. Apply the fix; rebuild + deploy `bin/simple`.
4. Confirm `scripts/check/check-f64-call-abi.shs` reports PASS.
