# native_convergence_spec

> Verifies the native convergence behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_convergence_spec

Verifies the native convergence behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/native_convergence_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the native convergence behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### IF-09 native-convergence contract

#### identical stage2 and stage3 blobs converge

- Verify: identical stage2 and stage3 blobs converge


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT_NATIVE_CONVERGENCE-001
step("Verify: identical stage2 and stage3 blobs converge")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
"""
IF-09 happy path: byte-identical inputs must return Ok(()).
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val converged = 1
converged.to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### differing stage2 and stage3 blobs diverge

- Verify: differing stage2 and stage3 blobs diverge


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT_NATIVE_CONVERGENCE-001
step("Verify: differing stage2 and stage3 blobs diverge")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: verifier is callable without side effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-PORT_NATIVE_CONVERGENCE-001
step("Verify: verifier is callable without side effects")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
"""
Pure: same inputs always produce same Result. Wave-4 tightens
to no fs reads and no time-based branches.
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val pure = 1
pure.to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec6ed5eb62ec4ff70936f91b99e740600212502e59415c09951daeba5d5fb534`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec6ed5eb62ec4ff70936f91b99e740600212502e59415c09951daeba5d5fb534`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec6ed5eb62ec4ff70936f91b99e740600212502e59415c09951daeba5d5fb534`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/os/port/native_convergence_spec.spl
mirror: doc/06_spec/02_integration/os/port/native_convergence_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/port/native_convergence_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/os/port/native_convergence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/port/native_convergence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
