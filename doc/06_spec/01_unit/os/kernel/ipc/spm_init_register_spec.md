# Spm Init Register Specification

> Tests covering init_services spm_port wiring.

```sdn id=spm_init_register_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spm_init_register_spec -> std
spm_init_register_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spm_init_register_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# spm_init_register_spec

Verifies the spm init register behaviour end to end so maintainers of this

## Scenarios

### init_services spm_port wiring

#### registers the SPM port during boot-time init

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### registers the well-known placeholder task id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
init_spm_port()
expect(spm_port_registered_task()).to_equal(spm_well_known_task_id())
```

</details>

#### well-known placeholder is non-zero (0 is the unregistered sentinel)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wk = spm_well_known_task_id()
expect(wk != (0 as u64)).to_equal(true)
```

</details>

#### init_spm_port is idempotent for the same placeholder id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
spm_port_reset()
val first = init_spm_port()
val second = init_spm_port()
expect(first).to_equal(true)
expect(second).to_equal(true)
expect(spm_port_registered_task()).to_equal(spm_well_known_task_id())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/spm_init_register_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d94c80e3c1a29b59defaf0ca92777563f532c071c5a2591f078d9eb0d84f10e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d94c80e3c1a29b59defaf0ca92777563f532c071c5a2591f078d9eb0d84f10e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d94c80e3c1a29b59defaf0ca92777563f532c071c5a2591f078d9eb0d84f10e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/os/kernel/ipc/spm_init_register_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/ipc/spm_init_register_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/ipc/spm_init_register_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/ipc/spm_init_register_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/ipc/spm_init_register_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/kernel/ipc/spm_init_register_spec.spl:22:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'registers the SPM port during boot-time init' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/ipc/spm_init_register_spec.spl:31:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'registers the well-known placeholder task id' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/ipc/spm_init_register_spec.spl:36:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'well-known placeholder is non-zero (0 is the unregistered sentinel)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/ipc/spm_init_register_spec.spl:40:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'init_spm_port is idempotent for the same placeholder id' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
