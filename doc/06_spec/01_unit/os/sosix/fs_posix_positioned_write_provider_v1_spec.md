# fs_posix_positioned_write_provider_v1_spec

> POSIX positioned-write provider contract specification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_posix_positioned_write_provider_v1_spec

POSIX positioned-write provider contract specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/fs_posix_positioned_write_provider_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

POSIX positioned-write provider contract specification.

## Scenarios

### SOSIX POSIX positioned-write provider v1

#### plans write_at from a certified registered buffer without a raw address

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans write_at from a certified registered buffer without a raw address
   - Expected: plan.reason equals `ready`
   - Expected: plan.api_id equals `2u32`
   - Expected: plan.payload.len() equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("plans write_at from a certified registered buffer without a raw address")
val plan = sosix_posix_plan_pwrite_v1(
    provider(true), SosixOperationId(slot: 2, generation: 3),
    4096, 1, 2, 0, 17)

expect(plan.accepted).to_be(true)
expect(plan.reason).to_equal("ready")
expect(plan.api_id).to_equal(2u32)
expect(plan.payload.len()).to_equal(88)
```

</details>

#### fails closed when the kernel registration provider is unavailable

- fails closed when the kernel registration provider is unavailable
   - Expected: plan.reason equals `positioned-write-provider-unavailable`
   - Expected: plan.status equals `SOSIX_POSIX_PWRITE_PROVIDER_UNAVAILABLE_V1`
   - Expected: plan.payload.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed when the kernel registration provider is unavailable")
val plan = sosix_posix_plan_pwrite_v1(
    provider(false), SosixOperationId(slot: 2, generation: 3),
    4096, 0, 3, 0, 17)

expect(plan.accepted).to_be(false)
expect(plan.reason).to_equal("positioned-write-provider-unavailable")
expect(plan.status).to_equal(SOSIX_POSIX_PWRITE_PROVIDER_UNAVAILABLE_V1)
expect(plan.payload.len()).to_equal(0)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c81564f0074f4345657049227a4b4747c942d45aac216c506d9d643d85e6bac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c81564f0074f4345657049227a4b4747c942d45aac216c506d9d643d85e6bac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c81564f0074f4345657049227a4b4747c942d45aac216c506d9d643d85e6bac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/sosix/fs_posix_positioned_write_provider_v1_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/fs_posix_positioned_write_provider_v1_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/fs_posix_positioned_write_provider_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/fs_posix_positioned_write_provider_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/fs_posix_positioned_write_provider_v1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/fs_posix_positioned_write_provider_v1_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans write_at from a certified registered buffer without a raw address' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fs_posix_positioned_write_provider_v1_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when the kernel registration provider is unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
