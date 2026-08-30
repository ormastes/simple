# SOSIX Host Library Capability Adapter

> REQ-SQ-014 library capability consumer contract.

The host owner is injected as a callback and is invoked only for a canonical
accepted plan. Invalid capabilities, blank identities, and forged public plan
values fail closed before callback dispatch.

Executable source:
`test/01_unit/os/sosix/host_library_capability_adapter_spec.spl`

# host_library_capability_adapter_spec

REQ-SQ-014 library capability consumer contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/host_library_capability_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

REQ-SQ-014 library capability consumer contract.

## Scenarios

### SOSIX host library capability adapter

#### dispatches one immutable authorized snapshot through the host callback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SQ-014
```

</details>

#### fails closed before callback dispatch for invalid or forged plans

- fails closed before callback dispatch for invalid or forged plans


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed before callback dispatch for invalid or forged plans")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-SQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `075fc7812b0fe9cbeeee1d6b23739fd979e37a546f3ffe448c28c91beecb8f41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `075fc7812b0fe9cbeeee1d6b23739fd979e37a546f3ffe448c28c91beecb8f41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `075fc7812b0fe9cbeeee1d6b23739fd979e37a546f3ffe448c28c91beecb8f41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/sosix/host_library_capability_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/host_library_capability_adapter_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/host_library_capability_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/host_library_capability_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/host_library_capability_adapter_spec.spl:24:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'dispatches one immutable authorized snapshot through the host callback' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/sosix/host_library_capability_adapter_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed before callback dispatch for invalid or forged plans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
