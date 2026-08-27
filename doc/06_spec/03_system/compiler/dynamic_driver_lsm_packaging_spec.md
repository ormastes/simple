# Dynamic Driver Lsm Packaging Specification

> Tests covering dynamic driver LSM packaging.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Driver Lsm Packaging Specification

## Scenarios

### dynamic driver LSM packaging

#### bin/simple compile --driver-mode=dynamic writes LSMF with SMF and DRVS bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bin/simple compile --driver-mode=dynamic writes LSMF with SMF and DRVS bytes
   - Expected: rt_file_write_text(src, "@driver(class = 2, vendor = 0x1B36, device = [0x000E], version = \"1.0\")\nfn driver_init():\n    return 0\n") is true
   - Expected: code equals `0`
   - Expected: rt_file_exists(out) is true
   - Expected: archive[0] equals `76`
   - Expected: archive[1] equals `83`
   - Expected: archive[2] equals `77`
   - Expected: archive[3] equals `70`
   - Expected: archive[smf_offset] equals `83`
   - Expected: archive[smf_offset + 1] equals `77`
   - Expected: archive[smf_offset + 2] equals `70`
   - Expected: archive[smf_offset + 3] equals `0`
   - Expected: contains_ascii(archive, [46, 100, 114, 118, 95, 109, 97, 110, 105, 102, 101, 115, 116]) is true
   - Expected: contains_ascii(archive, [83, 86, 82, 68]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple compile --driver-mode=dynamic writes LSMF with SMF and DRVS bytes")
val src = "/tmp/simple_dynamic_driver_lsm_packaging.spl"
val out = "/tmp/simple_dynamic_driver_lsm_packaging.lsm"
delete_if_exists(out)
expect(rt_file_write_text(src, "@driver(class = 2, vendor = 0x1B36, device = [0x000E], version = \"1.0\")\nfn driver_init():\n    return 0\n")).to_equal(true)

val (stdout, stderr, code) = rt_process_run("bin/simple", ["compile", "--driver-mode=dynamic", src, "-o", out])
expect(code).to_equal(0)
expect(rt_file_exists(out)).to_equal(true)

val archive = rt_file_read_bytes(out) ?? []
expect(archive[0]).to_equal(76)
expect(archive[1]).to_equal(83)
expect(archive[2]).to_equal(77)
expect(archive[3]).to_equal(70)

val smf_offset = le_u64(archive, 128 + 64)
expect(archive[smf_offset]).to_equal(83)
expect(archive[smf_offset + 1]).to_equal(77)
expect(archive[smf_offset + 2]).to_equal(70)
expect(archive[smf_offset + 3]).to_equal(0)
expect(contains_ascii(archive, [46, 100, 114, 118, 95, 109, 97, 110, 105, 102, 101, 115, 116])).to_equal(true)
expect(contains_ascii(archive, [83, 86, 82, 68])).to_equal(true)

delete_if_exists(src)
delete_if_exists(out)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/dynamic_driver_lsm_packaging_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dynamic driver LSM packaging.
- dynamic driver LSM packaging

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c83d6d96cdc875ba008243f93f117e07192351d0b36a2ceb1dcb5d4a91b5c183`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c83d6d96cdc875ba008243f93f117e07192351d0b36a2ceb1dcb5d4a91b5c183`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c83d6d96cdc875ba008243f93f117e07192351d0b36a2ceb1dcb5d4a91b5c183`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/compiler/dynamic_driver_lsm_packaging_spec.spl
mirror: doc/06_spec/03_system/compiler/dynamic_driver_lsm_packaging_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/dynamic_driver_lsm_packaging_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/dynamic_driver_lsm_packaging_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/dynamic_driver_lsm_packaging_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/dynamic_driver_lsm_packaging_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bin/simple compile --driver-mode=dynamic writes LSMF with SMF and DRVS bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
