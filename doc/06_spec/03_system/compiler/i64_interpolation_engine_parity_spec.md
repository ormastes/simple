# i64 string-interpolation engine-parity spec (REPRODUCER)

> Pins the exact defect: an `i64` rendered through string **interpolation**

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# i64 string-interpolation engine-parity spec (REPRODUCER)

Pins the exact defect: an `i64` rendered through string **interpolation**

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/i64_interpolation_engine_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pins the exact defect: an `i64` rendered through string **interpolation**
(`"{x}"`) truncated under the cranelift/JIT backend while the tree-walking
interpreter rendered it correctly.

Measured RED, stale seed `bin/release/x86_64-unknown-linux-gnu/simple`
(mtime 2026-08-16 22:59), on
`test/fixtures/repro/compiler/scalar_interpolation/scalar_interp_engine_parity_probe.spl`:

    interpreter                 jit
    I64_MAX_ANNOT=922337...807  I64_MAX_ANNOT=-1
    I64_MIN=-9223372036854775808 I64_MIN=0
    I64_POW62=4611686018427387904 I64_POW62=0
    I64_POW60=1152921504606846976 I64_POW60=-1152921504606846976

Root cause: `BoxInt` packs a RuntimeValue payload as `(value << 3) | TAG_INT`,
so only a signed 61-bit magnitude round-trips. The STRESS-F02 fix
(`stress_f02_i64_boxing_truncation_2026-07-17.md`) routed **direct `print(x)`
arguments** of type I64 through the `rt_raw_i64_to_string` bypass, but string
interpolation reaches the runtime through a *different* lowering helper
(`MirLowering::emit_to_string` in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`) which kept
only the U64 bypass and left I64 on the lossy BoxInt path. Same omission at
the explicit `rt_value_to_string(x)` builtin site in
`lowering_expr_builtin.rs`. Both now bypass for I64 as well as U64.

WHY THIS SPEC SPAWNS SUBPROCESSES: `bin/simple test` is the tree-walking
interpreter and never routes through the cranelift/JIT backend, even with
`SIMPLE_EXECUTION_MODE=jit` in its own environment. An in-body assertion can
therefore only ever observe the engine that was already correct -- it would
pass with the fix removed. The only way a spec can witness this defect is to
run the probe fixture as a child process under each engine and compare.

See doc/08_tracking/bug/stage3_numeric_interpolation_slot_corruption_2026-08-13.md.

## Scenarios

### i64 string interpolation renders identically under both engines

#### produces probe output under both engines at all

- produces probe output under both engines at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces probe output under both engines at all")
val interp_out = run_probe("interpreter")
val jit_out = run_probe("jit")
# Non-vacuity gate: an empty capture (earlyoom kill, missing binary)
# must not be mistaken for agreement between two empty strings.
assert_true(probe_field(interp_out, "I64_SMALL") == "42")
assert_true(probe_field(jit_out, "I64_SMALL") == "42")
```

</details>

#### renders i64::MAX exactly under the JIT, not -1

- renders i64::MAX exactly under the JIT, not -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders i64::MAX exactly under the JIT, not -1")
val jit_out = run_probe("jit")
assert_equal(probe_field(jit_out, "I64_MAX_ANNOT"), "9223372036854775807")
```

</details>

#### renders i64::MIN exactly under the JIT, not 0

- renders i64::MIN exactly under the JIT, not 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders i64::MIN exactly under the JIT, not 0")
val jit_out = run_probe("jit")
assert_equal(probe_field(jit_out, "I64_MIN"), "-9223372036854775808")
```

</details>

#### renders 2^62 exactly under the JIT, not 0

- renders 2^62 exactly under the JIT, not 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders 2^62 exactly under the JIT, not 0")
val jit_out = run_probe("jit")
assert_equal(probe_field(jit_out, "I64_POW62"), "4611686018427387904")
```

</details>

#### renders 2^60 exactly under the JIT, not sign-flipped

- renders 2^60 exactly under the JIT, not sign-flipped


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders 2^60 exactly under the JIT, not sign-flipped")
# The pre-existing interpreter-only spec
# test/03_system/compiler/i64_print_range_spec.spl asserts this value
# and passed throughout, because it never reached the JIT. Under the
# JIT this rendered as -1152921504606846976.
val jit_out = run_probe("jit")
assert_equal(probe_field(jit_out, "I64_POW60"), "1152921504606846976")
```

</details>

#### agrees with the interpreter on i64::MAX reached via .to_string()

- agrees with the interpreter on i64::MAX reached via .to_string()


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("agrees with the interpreter on i64::MAX reached via .to_string()")
val interp_out = run_probe("interpreter")
val jit_out = run_probe("jit")
assert_equal(probe_field(jit_out, "I64_MAX_TOSTRING"), probe_field(interp_out, "I64_MAX_TOSTRING"))
```

</details>

#### agrees with the interpreter on a function-return i64 and an array element

- agrees with the interpreter on a function-return i64 and an array element


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("agrees with the interpreter on a function-return i64 and an array element")
val interp_out = run_probe("interpreter")
val jit_out = run_probe("jit")
assert_equal(probe_field(jit_out, "I64_MAX_FNRET"), probe_field(interp_out, "I64_MAX_FNRET"))
assert_equal(probe_field(jit_out, "I64_MAX_ARRELEM"), probe_field(interp_out, "I64_MAX_ARRELEM"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87c6d0be36761011e2a02dc047f8c9888ba9039ec2b2bb6bb5d805cd5c5f90a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87c6d0be36761011e2a02dc047f8c9888ba9039ec2b2bb6bb5d805cd5c5f90a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87c6d0be36761011e2a02dc047f8c9888ba9039ec2b2bb6bb5d805cd5c5f90a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/i64_interpolation_engine_parity_spec.spl
mirror: doc/06_spec/03_system/compiler/i64_interpolation_engine_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/i64_interpolation_engine_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/i64_interpolation_engine_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/i64_interpolation_engine_parity_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces probe output under both engines at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/i64_interpolation_engine_parity_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders i64::MAX exactly under the JIT, not -1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/i64_interpolation_engine_parity_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders i64::MIN exactly under the JIT, not 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
