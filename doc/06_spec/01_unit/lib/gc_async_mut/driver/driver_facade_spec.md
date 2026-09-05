# Driver Facade Specification

> Tests covering gc_async_mut driver facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Facade Specification

## Scenarios

### gc_async_mut driver facade

#### re-exports driver contracts and null block operations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports driver contracts and null block operations
   - Expected: errno_of(DriverError.BadArg) equals `22`
   - Expected: null_block_probe(dev).unwrap() equals `ProbeResult.Accept`
   - Expected: handle.value equals `1`
   - Expected: null_block_ioctl(handle, cmd).unwrap() equals `42`
   - Expected: manifest.abi_rev equals `DRVS_ABI_REV`
   - Expected: null_block_abi_rev() equals `DRVS_ABI_REV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports driver contracts and null block operations")
expect(errno_of(DriverError.BadArg)).to_equal(22)
val dev = DeviceId(value: 0, dclass: DriverClass.Block)
expect(null_block_probe(dev).unwrap()).to_equal(ProbeResult.Accept)
val handle = null_block_attach(dev).unwrap()
expect(handle.value).to_equal(1)
val cmd = IoctlCmd(code: 42, arg: 0)
expect(null_block_ioctl(handle, cmd).unwrap()).to_equal(42)
val manifest = DriverManifest.for_driver("null", "0.1", DriverClass.Block, 0, [0])
expect(manifest.abi_rev).to_equal(DRVS_ABI_REV)
expect(null_block_abi_rev()).to_equal(DRVS_ABI_REV)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/driver/driver_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut driver facade.
- gc_async_mut driver facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `f52b947e0dfee8d3dc1c044b48a61ab519cddf8aef5c3a68fe8fcc7ca859044b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f52b947e0dfee8d3dc1c044b48a61ab519cddf8aef5c3a68fe8fcc7ca859044b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f52b947e0dfee8d3dc1c044b48a61ab519cddf8aef5c3a68fe8fcc7ca859044b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/driver/driver_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/driver/driver_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/driver/driver_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/driver/driver_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/driver/driver_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/driver/driver_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports driver contracts and null block operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
