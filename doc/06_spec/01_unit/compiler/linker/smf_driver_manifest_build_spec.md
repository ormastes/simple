# Smf Driver Manifest Build Specification

> Tests covering SMF driver manifest build.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Driver Manifest Build Specification

## Scenarios

### SMF driver manifest build

#### emits a .drv_manifest section when build options carry DRVS bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a .drv_manifest section when build options carry DRVS bytes
   - Expected: section_count equals `2`
   - Expected: smf[section_table + 64] equals `14`
   - Expected: drv_size equals `16`
   - Expected: le_u32(smf, drv_offset) equals `0x44525653`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a .drv_manifest section when build options carry DRVS bytes")
var opts = SmfBuildOptions.create(Target.x86_64_unknown_linux_gnu())
opts.driver_manifest_bytes = [
    0x53, 0x56, 0x52, 0x44,  # DRVS little endian
    0, 0, 1, 0,              # kind, class, abi_rev
    0, 0, 0, 0,              # vendor
    0, 0, 0, 0               # device_count
]

val smf = generate_smf_with_options([0xC3], opts)
val header = smf.len() - 128
val section_count = le_u32(smf, header + 16)
val section_table = le_u64(smf, header + 20)

expect(section_count).to_equal(2)
expect(find_byte(smf, 14)).to_be_greater_than(0)
expect(smf[section_table + 64]).to_equal(14)

val drv_offset = le_u64(smf, section_table + 64 + 8)
val drv_size = le_u64(smf, section_table + 64 + 16)
expect(drv_size).to_equal(16)
expect(le_u32(smf, drv_offset)).to_equal(0x44525653)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_driver_manifest_build_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SMF driver manifest build.
- SMF driver manifest build

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

- Canonical SPipe generation for source `b748b44c012e7a036c5a5f2d7b62d114362e258a17ff59ce0bb97b95fbd19eb5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b748b44c012e7a036c5a5f2d7b62d114362e258a17ff59ce0bb97b95fbd19eb5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b748b44c012e7a036c5a5f2d7b62d114362e258a17ff59ce0bb97b95fbd19eb5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/linker/smf_driver_manifest_build_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/smf_driver_manifest_build_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/smf_driver_manifest_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/smf_driver_manifest_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/smf_driver_manifest_build_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/smf_driver_manifest_build_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a .drv_manifest section when build options carry DRVS bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
