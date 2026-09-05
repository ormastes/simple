# JIT Defect 2 guard: named-fn-as-value must fail loudly, never silently

> Defect 1's existing guard (`first_lambda_function_impl` in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JIT Defect 2 guard: named-fn-as-value must fail loudly, never silently

Defect 1's existing guard (`first_lambda_function_impl` in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## The defect (before this guard)

Defect 1's existing guard (`first_lambda_function_impl` in
src/compiler_rust/compiler/src/codegen/jit.rs) refuses any module containing
a `MirInst::ClosureCreate`, which is emitted only for lambda literals. A
NAMED function passed as a value (`val g = add_one`, or `apply(add_one, 41)`)
takes a different MIR lowering path (`lower_global_expr`'s "static method
reference" fallback -> `MirInst::GlobalLoad`), emits no `ClosureCreate`, and
so passed the guard undetected. `compile_indirect_call` then dereferenced the
bare function code address as if it pointed at a closure struct, calling
garbage. Result measured 2026-08-06/07: an ASLR-shaped wrong i64, exit 0, NO
diagnostic -- the single worst case in this defect family, because "replace
the lambda with a named fn" (the obvious workaround for Defect 1) turns a
slow-but-correct program into a fast-but-wrong one.

## The fix

`Self::first_named_fn_value_load` (jit.rs) scans the MIR module for any
`GlobalLoad { global_name, .. }` whose name is a declared function but NOT a
declared global variable -- exactly the shape `lower_global_expr` emits for a
function-as-value reference, and not the shape emitted for an ordinary direct
call (which lowers via `MirInst::Call`/`CallTarget`, never through
`GlobalLoad`). A match refuses the whole module at JIT-compile time, matching
Defect 1's existing loud fallback: an `[INFO] ... falling back to
interpreter` line naming the offending function, then correct execution on
the interpreter.

## Why this spec spawns a probe instead of asserting inline

**JIT-only.** `bin/simple test` runs the interpreter lane exclusively (see
.claude/rules/testing.md), which never had this defect -- an in-process
`expect(...)` on this repro would be vacuously green both before and after
the fix. The real work is in
`jit_named_fn_ref_guard_jit_probe.spl`, a runnable program with `fn main`
that reproduces fixture f06 from
test/fixtures/repro/compiler/jit_closure/f06_named_fn_as_value.spl, spawned
here under an explicitly NAMED engine.

Sabotage receipt (measured against this session's binary, before vs. after
the `first_named_fn_value_load` guard landed):

    unguarded / jit        -> f06 marker result=140359598346673 (garbage, no diagnostic)
    unguarded / interpret  -> f06 marker result=42
    guarded   / jit         -> [INFO] ... falling back to interpreter: ... 'main' loads a
                                named function as a callable value ...; f06 marker result=42
    guarded   / interpret   -> f06 marker result=42

Pattern and adoption notes: doc/07_guide/infra/testing/spec_engine_reach.md
Helper tier: src/lib/nogc_sync_mut/spec/engine_probe.spl

Run with: bin/simple test test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl

## Scenarios

### JIT guard for named-fn-as-value (Defect 2, out of process)

#### passes the probe under the interpreter

- passes the probe under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the probe under the interpreter")
# Control column. The interpreter never had this defect, so this arm
# failing means the probe or the harness broke, not the JIT guard.
assert_true(engine_stdout(_PROBE, "interpret").contains(_PASS))
```

</details>

#### passes the probe under the cranelift JIT once the guard forces a correct fallback

- passes the probe under the cranelift JIT once the guard forces a correct fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the probe under the cranelift JIT once the guard forces a correct fallback")
# The arm that carries the weight. Before the guard this printed a
# garbage i64 (pass=0 fail=1); the guard makes the JIT refuse the
# module and fall back to the interpreter, so this now agrees with
# the interpreter arm above.
assert_true(engine_stdout(_PROBE, "jit").contains(_PASS))
```

</details>

#### rejects an unrecognised engine name instead of silently using the JIT

- rejects an unrecognised engine name instead of silently using the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unrecognised engine name instead of silently using the JIT")
# SIMPLE_EXECUTION_MODE falls back to JIT on any unknown value --
# notably "native", which is NOT a mode -- so an A/B built on an
# unvalidated name would compare the JIT against itself.
assert_false(is_known_engine("interp"))
assert_false(is_known_engine("native"))
assert_true(is_known_engine("jit"))
assert_true(is_known_engine("interpret"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e14d5f94f9519879f60bf76d34495a42230c9694c8441fcb39ab9a02f01dcc6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e14d5f94f9519879f60bf76d34495a42230c9694c8441fcb39ab9a02f01dcc6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e14d5f94f9519879f60bf76d34495a42230c9694c8441fcb39ab9a02f01dcc6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/jit_named_fn_ref_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/jit_named_fn_ref_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/jit_named_fn_ref_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes the probe under the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes the probe under the cranelift JIT once the guard forces a correct fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unrecognised engine name instead of silently using the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
