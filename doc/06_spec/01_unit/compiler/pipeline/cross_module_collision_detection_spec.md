# Cross Module Collision Detection Specification

> Tests covering cross-module collision detection covers every collision shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Module Collision Detection Specification

## Scenarios

### cross-module collision detection covers every collision shape

#### names every colliding symbol under default settings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- names every colliding symbol under default settings
- Run the collision probe with NO diagnostic env vars — this is what a developer, a CI lane and a bootstrap actually see
- The run must have happened at all — otherwise every absence below is vacuous
- Differing-signature collision: already detected today, and must stay detected
- Identical-signature PRIVATE collision — the shape no other tool can detect, and the one that silently returned A_private for B's call in this same run
- Identical-signature PUBLIC collision — same shape, and proof the defect is not specific to the `_` prefix
- Each warning must carry the stable collision-family tag, so a reworded message cannot silently void this spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names every colliding symbol under default settings")
step("Run the collision probe with NO diagnostic env vars — this is what a developer, a CI lane and a bootstrap actually see")
val out = probe_stderr_with("")

step("The run must have happened at all — otherwise every absence below is vacuous")
expect(out).to_contain("XMOD_COLLISION PROBE")

step("Differing-signature collision: already detected today, and must stay detected")
expect(out).to_contain("shared_arity")

step("Identical-signature PRIVATE collision — the shape no other tool can detect, and the one that silently returned A_private for B's call in this same run")
expect(out).to_contain("_shared_helper")

step("Identical-signature PUBLIC collision — same shape, and proof the defect is not specific to the `_` prefix")
expect(out).to_contain("shared_public")

step("Each warning must carry the stable collision-family tag, so a reworded message cannot silently void this spec")
expect(out).to_contain("[compiler_cross_module_private_symbol_collision]")
```

</details>

#### reports a same-signature collision through the detector itself

- reports a same-signature collision through the detector itself
- Run once with the same-signature diagnostic explicitly enabled
- This arm is the CONTROL: it proves the detector works and that any red in the previous example is about the DEFAULT being off, not about a broken probe or fixture
- The stable collision-family tag must be present here too


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a same-signature collision through the detector itself")
step("Run once with the same-signature diagnostic explicitly enabled")
val opted_in = probe_stderr_with("SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1")

step("This arm is the CONTROL: it proves the detector works and that any red in the previous example is about the DEFAULT being off, not about a broken probe or fixture")
expect(opted_in).to_contain("_shared_helper")
expect(opted_in).to_contain("shared_public")

step("The stable collision-family tag must be present here too")
expect(opted_in).to_contain("[compiler_cross_module_private_symbol_collision]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/pipeline/cross_module_collision_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cross-module collision detection covers every collision shape.
- cross-module collision detection covers every collision shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `4e07dbf4ca5c4d7894b2d630947e0efdc068b6975002df0f01372e6bea43d2fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e07dbf4ca5c4d7894b2d630947e0efdc068b6975002df0f01372e6bea43d2fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e07dbf4ca5c4d7894b2d630947e0efdc068b6975002df0f01372e6bea43d2fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/pipeline/cross_module_collision_detection_spec.spl
mirror: doc/06_spec/01_unit/compiler/pipeline/cross_module_collision_detection_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/pipeline/cross_module_collision_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/pipeline/cross_module_collision_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/pipeline/cross_module_collision_detection_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names every colliding symbol under default settings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/pipeline/cross_module_collision_detection_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a same-signature collision through the detector itself' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
