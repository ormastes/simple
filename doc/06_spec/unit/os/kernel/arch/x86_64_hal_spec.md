# x86_64_hal_spec

> x86_64 HAL aggregate contract tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64_hal_spec

x86_64 HAL aggregate contract tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/x86_64_hal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

x86_64 HAL aggregate contract tests.

These tests cover pure metadata exposed by the aggregate HAL without invoking
privileged instructions such as CLI, HLT, CR3 writes, or port I/O.

## Scenarios

### x86_64 HAL aggregate

#### exposes x86_64 CPU identity metadata

- exposes x86_64 CPU identity metadata
   - Expected: hal.cpu.cpu_id() equals `0`
   - Expected: hal.cpu.cpu_address_width() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes x86_64 CPU identity metadata")
val hal = create_x86_64_hal()

expect(hal.cpu.cpu_id()).to_equal(0)
expect(hal.cpu.cpu_address_width()).to_equal(64)
```

</details>

#### exposes x86_64 paging geometry

- exposes x86_64 paging geometry
   - Expected: hal.paging.page_size() equals `4096`
   - Expected: hal.paging.address_levels() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes x86_64 paging geometry")
val hal = create_x86_64_hal()

expect(hal.paging.page_size()).to_equal(4096)
expect(hal.paging.address_levels()).to_equal(4)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c9a9223696222bec0367ed058d376e12588bf4570eb0ddd2b0a7fbfa8af819ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c9a9223696222bec0367ed058d376e12588bf4570eb0ddd2b0a7fbfa8af819ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c9a9223696222bec0367ed058d376e12588bf4570eb0ddd2b0a7fbfa8af819ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/arch/x86_64_hal_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/x86_64_hal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/x86_64_hal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/x86_64_hal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/x86_64_hal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/arch/x86_64_hal_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes x86_64 CPU identity metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_64_hal_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes x86_64 paging geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
