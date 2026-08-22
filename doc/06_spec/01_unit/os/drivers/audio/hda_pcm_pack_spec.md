# hda_pcm_pack_spec

> Verifies the hda pcm pack behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hda_pcm_pack_spec

Verifies the hda pcm pack behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/audio/hda_pcm_pack_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the hda pcm pack behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### HDA application PCM packing

#### packs four signed 16-bit samples into one scalar DMA store

- Verify: packs four signed 16-bit samples into one scalar DMA store
   - Expected: pcm_i16_pack_4(32767, -32768, 1, -1) equals `-281468534226945)  # oracle: pinned constant asserted by this scenario`
   - Expected: pcm_i16_pack_4(0, 0, 0, 0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-008
step("Verify: packs four signed 16-bit samples into one scalar DMA store")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(pcm_i16_pack_4(32767, -32768, 1, -1)).to_equal(-281468534226945)  # oracle: pinned constant asserted by this scenario
expect(pcm_i16_pack_4(0, 0, 0, 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### clamps samples before packing

- Verify: clamps samples before packing
   - Expected: pcm_i16_pack_4(40000, -40000, 0, 0) equals `2147516415)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-008
step("Verify: clamps samples before packing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(pcm_i16_pack_4(40000, -40000, 0, 0)).to_equal(2147516415)  # oracle: pinned constant asserted by this scenario
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

- Canonical SPipe generation for source `369bb29e6a8ad168dab2fe010e610e72ada3a1fdcef7df4718be4ad6a864da99`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `369bb29e6a8ad168dab2fe010e610e72ada3a1fdcef7df4718be4ad6a864da99`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `369bb29e6a8ad168dab2fe010e610e72ada3a1fdcef7df4718be4ad6a864da99`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/drivers/audio/hda_pcm_pack_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/audio/hda_pcm_pack_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/drivers/audio/hda_pcm_pack_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/drivers/audio/hda_pcm_pack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/audio/hda_pcm_pack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
