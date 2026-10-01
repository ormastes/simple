# Scalar-interpolation engine-parity SWEEP (DETECTION spec)

> This is the *class* guard for the defect its sibling reproducer pins

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scalar-interpolation engine-parity SWEEP (DETECTION spec)

This is the *class* guard for the defect its sibling reproducer pins

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This is the *class* guard for the defect its sibling reproducer pins
(`i64_interpolation_engine_parity_spec.spl`). It does not name any single
magnitude or type. It asserts a structural invariant:

  **Every `KEY=value` line the probe fixture emits must be byte-identical
  between `SIMPLE_EXECUTION_MODE=interpreter` and `SIMPLE_EXECUTION_MODE=jit`.**

The defect class is "a scalar-to-text renderer reached through string
interpolation loses information on one engine but not the other". There are
several sibling renderers behind the same lowering helper
(`MirLowering::emit_to_string`, `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`):
`rt_raw_u64_to_string`, `rt_raw_i64_to_string`, `rt_value_bool`, `BoxFloat`,
`BoxInt` for the narrow int types, plus the flat-optional bypasses
(`rt_opt_i64_to_string` / `rt_opt_bool_to_string` / `rt_opt_f64_to_string`).
Each has independently been the site of a truncation or mis-tagging bug:

  - `stress_f02_i64_boxing_truncation_2026-07-17.md` (I64/U64 61-bit payload)
  - `interp_index_of_digit_leading_literal_2026-07-22.md` (flat-optional raw
    payload misread as tag bits)
  - `stage3_numeric_interpolation_slot_corruption_2026-08-13.md` (a numeric
    render overwrote an adjacent array backing pointer)

A per-value spec catches only the value it names. This one fails the moment
ANY line diverges, so adding a shape to the probe fixture extends the guard
with no spec edit -- which is the point: the pre-existing interpreter-only
spec `i64_print_range_spec.spl` named four exact magnitudes, ran only under
the tree-walking interpreter, and stayed green through the entire JIT
regression including for the very 2^60 value it asserts.

WHY SUBPROCESSES: `bin/simple test` is the tree-walking interpreter and never
routes through the cranelift/JIT backend regardless of its own
`SIMPLE_EXECUTION_MODE`. A spec body cannot exercise a JIT defect at all;
only a child-process comparison can. `env` is invoked directly because the
resource test-slot wrapper does not propagate environment variables to the
child binary.

## Scenarios

### every interpolated scalar renders identically under both engines

#### captured a non-trivial number of payload lines from both engines

- captured a non-trivial number of payload lines from both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captured a non-trivial number of payload lines from both engines")
# Non-vacuity gate, and it is absolute: two empty captures agree
# trivially, so a comparison over 0 lines is a failure, never a pass.
# earlyoom kills `simple` first on this host, so an empty capture is
# a real and frequent outcome that must not read as green.
val interp_lines = payload_lines(run_probe("interpreter"))
val jit_lines = payload_lines(run_probe("jit"))
assert_true(interp_lines.len() >= 15)
assert_true(jit_lines.len() >= 15)
```

</details>

#### emits the same number of payload lines under both engines

- emits the same number of payload lines under both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits the same number of payload lines under both engines")
val interp_lines = payload_lines(run_probe("interpreter"))
val jit_lines = payload_lines(run_probe("jit"))
assert_equal(jit_lines.len(), interp_lines.len())
```

</details>

#### emits byte-identical payload lines under both engines

- emits byte-identical payload lines under both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits byte-identical payload lines under both engines")
val interp_lines = payload_lines(run_probe("interpreter"))
val jit_lines = payload_lines(run_probe("jit"))
assert_true(interp_lines.len() >= 15)
assert_equal(jit_lines.len(), interp_lines.len())
var divergent: [text] = []
var i = 0
while i < interp_lines.len():
    if interp_lines[i] != jit_lines[i]:
        divergent.push("interpreter=" + interp_lines[i] + " jit=" + jit_lines[i])
    i = i + 1
# Name the offenders in the failure, so a regression identifies which
# renderer broke rather than only that something did.
assert_equal(divergent.len(), 0)
```

</details>

#### renders no scalar as a bare -1 or 0 under the JIT unless the interpreter does too

- renders no scalar as a bare -1 or 0 under the JIT unless the interpreter does too


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders no scalar as a bare -1 or 0 under the JIT unless the interpreter does too")
# Shape-level canary independent of the line-by-line diff above:
# -1 and 0 are the two signature outputs of a lost `(v << 3)` payload
# (top bits shifted out, or the single set bit shifted past bit 63).
val interp_lines = payload_lines(run_probe("interpreter"))
val jit_lines = payload_lines(run_probe("jit"))
assert_true(interp_lines.len() >= 15)
var interp_suspicious = 0
for line in interp_lines:
    if line.ends_with("=-1") or line.ends_with("=0"):
        interp_suspicious = interp_suspicious + 1
var jit_suspicious = 0
for line in jit_lines:
    if line.ends_with("=-1") or line.ends_with("=0"):
        jit_suspicious = jit_suspicious + 1
assert_equal(jit_suspicious, interp_suspicious)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `fc61e993d86803a79c499b28b43709e9cb0e92b871438168c7d6e88e484b7da4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc61e993d86803a79c499b28b43709e9cb0e92b871438168c7d6e88e484b7da4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc61e993d86803a79c499b28b43709e9cb0e92b871438168c7d6e88e484b7da4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.spl
mirror: doc/06_spec/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captured a non-trivial number of payload lines from both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the same number of payload lines under both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits byte-identical payload lines under both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
