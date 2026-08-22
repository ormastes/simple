# spm_init_register_spec

> Verifies the spm init register behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spm_init_register_spec

Verifies the spm init register behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/spm_init_register_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the spm init register behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### init_services spm_port wiring

#### registers the SPM port during boot-time init

- Verify: registers the SPM port during boot-time init
   - Expected: spm_port_is_registered() is false
   - Expected: ok is true
   - Expected: spm_port_is_registered() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_INIT_REGISTER-001
step("Verify: registers the SPM port during boot-time init")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
expect(spm_port_is_registered()).to_equal(false)
val ok = init_spm_port()
expect(ok).to_equal(true)
expect(spm_port_is_registered()).to_equal(true)
```

</details>

#### registers the well-known placeholder task id

- Verify: registers the well-known placeholder task id
   - Expected: spm_port_registered_task() equals `spm_well_known_task_id()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_INIT_REGISTER-001
step("Verify: registers the well-known placeholder task id")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
init_spm_port()
expect(spm_port_registered_task()).to_equal(spm_well_known_task_id())
```

</details>

#### well-known placeholder is non-zero (0 is the unregistered sentinel)

- Verify: well-known placeholder is non-zero (0 is the unregistered sentinel)
   - Expected: wk != (0 as u64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_INIT_REGISTER-001
step("Verify: well-known placeholder is non-zero (0 is the unregistered sentinel)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wk = spm_well_known_task_id()
expect(wk != (0 as u64)).to_equal(true)
```

</details>

#### init_spm_port is idempotent for the same placeholder id

- Verify: init_spm_port is idempotent for the same placeholder id
   - Expected: first is true
   - Expected: second is true
   - Expected: spm_port_registered_task() equals `spm_well_known_task_id()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-IPC_SPM_INIT_REGISTER-001
step("Verify: init_spm_port is idempotent for the same placeholder id")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
spm_port_reset()
val first = init_spm_port()
val second = init_spm_port()
expect(first).to_equal(true)
expect(second).to_equal(true)
expect(spm_port_registered_task()).to_equal(spm_well_known_task_id())
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b3ead9575341362e8a622825988909acface876957ac80b74dcd9b137a799449`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3ead9575341362e8a622825988909acface876957ac80b74dcd9b137a799449`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3ead9575341362e8a622825988909acface876957ac80b74dcd9b137a799449`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/ipc/spm_init_register_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/ipc/spm_init_register_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/ipc/spm_init_register_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/ipc/spm_init_register_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/ipc/spm_init_register_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
