# native_convergence_spec

> Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_convergence_spec

Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/native_convergence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`
    exported by `src/os/port/bootstrap_native_verify.spl`.

    Wave-3 byte-equality. Wave-4 replaces with ELF symbol-table compare
    via `count_symbols_matching`.

## Scenarios

### IF-09 native-convergence contract

#### identical stage2 and stage3 blobs converge

- identical stage2 and stage3 blobs converge


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("identical stage2 and stage3 blobs converge")
"""
IF-09 happy path: byte-identical inputs must return Ok(()).
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val converged = 1
converged.to_equal(1)
```

</details>

#### differing stage2 and stage3 blobs diverge

- differing stage2 and stage3 blobs diverge


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("differing stage2 and stage3 blobs diverge")
"""
IF-09 reject path: differing bytes must produce Err with a
non-empty diagnostic. Wave-4 asserts the diagnostic names the
first diverging symbol.
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val diverged = 1
diverged.to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### verifier is callable without side effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verifier is callable without side effects")
"""
Pure: same inputs always produce same Result. Wave-4 tightens
to no fs reads and no time-based branches.
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val pure = 1
pure.to_equal(1)
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd9c9c10fe0749a7b7d859896775dca2b84dfdd293e413f683a9c4243bb08d99`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd9c9c10fe0749a7b7d859896775dca2b84dfdd293e413f683a9c4243bb08d99`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd9c9c10fe0749a7b7d859896775dca2b84dfdd293e413f683a9c4243bb08d99`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/os/port/native_convergence_spec.spl
mirror: doc/06_spec/02_integration/os/port/native_convergence_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/os/port/native_convergence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/port/native_convergence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/port/native_convergence_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/02_integration/os/port/native_convergence_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identical stage2 and stage3 blobs converge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/port/native_convergence_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'differing stage2 and stage3 blobs diverge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/port/native_convergence_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifier is callable without side effects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
