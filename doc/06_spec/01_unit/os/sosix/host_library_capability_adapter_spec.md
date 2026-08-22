# host_library_capability_adapter_spec

> Verifies the host library capability adapter behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# host_library_capability_adapter_spec

Verifies the host library capability adapter behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/host_library_capability_adapter_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the host library capability adapter behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SOSIX host library capability adapter

#### dispatches one immutable authorized snapshot through the host callback

- Verify: dispatches one immutable authorized snapshot through the host callback


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-014
step("Verify: dispatches one immutable authorized snapshot through the host callback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val snapshot = SosixHostLibrarySnapshot(
    library: SosixCapabilityRef(slot: 7, generation: 3),
    logical_name: "renderer", abi: "engine2d-v1")
val plan = sosix_host_library_plan(snapshot)
expect(plan.accepted).to_be(true)
expect(sosix_host_library_dispatch(plan, accept_expected)).to_be(true)
```

</details>

#### fails closed before callback dispatch for invalid or forged plans

- Verify: fails closed before callback dispatch for invalid or forged plans


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-014
step("Verify: fails closed before callback dispatch for invalid or forged plans")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val invalid = SosixHostLibrarySnapshot(
    library: SosixCapabilityRef(slot: 7, generation: 0),
    logical_name: "renderer", abi: "engine2d-v1")
expect(sosix_host_library_plan(invalid).reason).to_equal(
    "invalid-library-capability")
val valid = SosixHostLibrarySnapshot(
    library: SosixCapabilityRef(slot: 7, generation: 3),
    logical_name: "renderer", abi: "engine2d-v1")
val forged = SosixHostLibraryPlan(
    accepted: true, reason: "forged", snapshot: valid)
expect(sosix_host_library_dispatch(forged, accept_expected)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1dad7fac51afc0c0cf7065d1ff4275e36f4b75b0f854fa6d546d095e747a2f57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1dad7fac51afc0c0cf7065d1ff4275e36f4b75b0f854fa6d546d095e747a2f57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1dad7fac51afc0c0cf7065d1ff4275e36f4b75b0f854fa6d546d095e747a2f57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/sosix/host_library_capability_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/host_library_capability_adapter_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/host_library_capability_adapter_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/sosix/host_library_capability_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/host_library_capability_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
