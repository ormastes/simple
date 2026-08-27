# Aspect Instrumentation Readiness Ladder Specification

> Implements startup_perf_architecture_2026-08-17.md §7.4: a module declares

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aspect Instrumentation Readiness Ladder Specification

Implements startup_perf_architecture_2026-08-17.md §7.4: a module declares

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/aspect_readiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Implements startup_perf_architecture_2026-08-17.md §7.4: a module declares
one readiness level (none < boundary < full), and an aspect requiring a
level of instrumentation is treated according to the module's VERIFIED
level — never according to a bare assertion.

## Scenarios

### Readiness ladder — each level treated per its meaning (§7.4)

#### none: no instrumentation sites — every activation answer is needs_rebuild

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- none: no instrumentation sites — every activation answer is needs_rebuild


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("none: no instrumentation sites — every activation answer is needs_rebuild")
expect readiness_declare("stage0.loader", READINESS_NONE, 0, 0) == true
expect readiness_level("stage0.loader") == READINESS_NONE
expect readiness_admits("stage0.loader", READINESS_BOUNDARY) == false
expect readiness_absence("stage0.loader", READINESS_BOUNDARY) == READINESS_NEEDS_REBUILD
expect readiness_absence("stage0.loader", READINESS_FULL) == READINESS_NEEDS_REBUILD
# a none module still satisfies an aspect that needs no instrumentation
expect readiness_admits("stage0.loader", READINESS_NONE) == true
```

</details>

#### boundary: lifecycle slots admit boundary activation, full tracing is refused with needs_instrumented_build

- boundary: lifecycle slots admit boundary activation, full tracing is refused with needs_instrumented_build


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boundary: lifecycle slots admit boundary activation, full tracing is refused with needs_instrumented_build")
expect readiness_declare("interp.fast", READINESS_BOUNDARY, 12, 0) == true
expect readiness_admits("interp.fast", READINESS_BOUNDARY) == true
expect readiness_absence("interp.fast", READINESS_BOUNDARY) == READINESS_READY
expect readiness_admits("interp.fast", READINESS_FULL) == false
expect readiness_absence("interp.fast", READINESS_FULL) == READINESS_NEEDS_INSTRUMENTED_BUILD
```

</details>

#### full: instrumented build admits every level up to full tracing

- full: instrumented build admits every level up to full tracing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full: instrumented build admits every level up to full tracing")
expect readiness_declare("interp.debug", READINESS_FULL, 12, 340) == true
expect readiness_admits("interp.debug", READINESS_NONE) == true
expect readiness_admits("interp.debug", READINESS_BOUNDARY) == true
expect readiness_admits("interp.debug", READINESS_FULL) == true
expect readiness_absence("interp.debug", READINESS_FULL) == READINESS_READY
```

</details>

#### unknown module is NOT ready — absence of a claim is never readiness

- unknown module is NOT ready — absence of a claim is never readiness


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown module is NOT ready — absence of a claim is never readiness")
expect readiness_admits("never.declared", READINESS_BOUNDARY) == false
expect readiness_absence("never.declared", READINESS_NONE) == READINESS_UNKNOWN_MODULE
```

</details>

#### moving up a rung requires evidence: promotion with sites is accepted and changes the verdict

- moving up a rung requires evidence: promotion with sites is accepted and changes the verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moving up a rung requires evidence: promotion with sites is accepted and changes the verdict")
expect readiness_declare("svc.cache", READINESS_BOUNDARY, 4, 0) == true
expect readiness_admits("svc.cache", READINESS_FULL) == false
expect readiness_promote("svc.cache", READINESS_FULL, 4, 90) == true
expect readiness_level("svc.cache") == READINESS_FULL
expect readiness_admits("svc.cache", READINESS_FULL) == true
expect readiness_last_error() == ""
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `33baa0c1ebdac4ce5a2431c2c885597e7ea68e8ae23f161669d9a410653e9981`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33baa0c1ebdac4ce5a2431c2c885597e7ea68e8ae23f161669d9a410653e9981`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33baa0c1ebdac4ce5a2431c2c885597e7ea68e8ae23f161669d9a410653e9981`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/aspect_readiness_spec.spl
mirror: doc/06_spec/01_unit/lib/aspect_readiness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/aspect_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/aspect_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/aspect_readiness_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'none: no instrumentation sites — every activation answer is needs_rebuild' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_readiness_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boundary: lifecycle slots admit boundary activation, full tracing is refused with needs_instrumented_build' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_readiness_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'full: instrumented build admits every level up to full tracing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
