# Hda Pcm Pack Specification

> Tests covering HDA application PCM packing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hda Pcm Pack Specification

## Scenarios

### HDA application PCM packing

#### packs four signed 16-bit samples into one scalar DMA store

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- packs four signed 16-bit samples into one scalar DMA store
   - Expected: pcm_i16_pack_4(32767, -32768, 1, -1) equals `-281468534226945`
   - Expected: pcm_i16_pack_4(0, 0, 0, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("packs four signed 16-bit samples into one scalar DMA store")
expect(pcm_i16_pack_4(32767, -32768, 1, -1)).to_equal(-281468534226945)
expect(pcm_i16_pack_4(0, 0, 0, 0)).to_equal(0)
```

</details>

#### clamps samples before packing

- clamps samples before packing
   - Expected: pcm_i16_pack_4(40000, -40000, 0, 0) equals `2147516415`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clamps samples before packing")
expect(pcm_i16_pack_4(40000, -40000, 0, 0)).to_equal(2147516415)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/audio/hda_pcm_pack_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HDA application PCM packing.
- HDA application PCM packing

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
- `REQ-003`
- `REQ-008`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55e16a39c8d872d65b2cb3c1e5a9d29fbaa3326fe0ce332313c0e66964397b23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55e16a39c8d872d65b2cb3c1e5a9d29fbaa3326fe0ce332313c0e66964397b23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55e16a39c8d872d65b2cb3c1e5a9d29fbaa3326fe0ce332313c0e66964397b23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/drivers/audio/hda_pcm_pack_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/audio/hda_pcm_pack_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/drivers/audio/hda_pcm_pack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/audio/hda_pcm_pack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/audio/hda_pcm_pack_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/drivers/audio/hda_pcm_pack_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/drivers/audio/hda_pcm_pack_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs four signed 16-bit samples into one scalar DMA store' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/audio/hda_pcm_pack_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clamps samples before packing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
