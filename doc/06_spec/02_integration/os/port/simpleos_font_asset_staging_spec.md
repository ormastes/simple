# Simpleos Font Asset Staging Specification

> Tests covering SimpleOS pinned font asset staging.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Font Asset Staging Specification

## Scenarios

### SimpleOS pinned font asset staging

#### should use the pinned Noto Sans Mono path length and hash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should use the pinned Noto Sans Mono path length and hash
- Inspect the default SimpleOS font identity
   - Expected: font.local_path equals `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`
   - Expected: font.byte_len equals `1708408`
   - Expected: font.sha256 equals `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should use the pinned Noto Sans Mono path length and hash")
step("Inspect the default SimpleOS font identity")
val font = simpleos_default_font_asset_candidate()
expect(font.local_path).to_equal("assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf")
expect(font.byte_len).to_equal(1708408)
expect(font.sha256).to_equal("2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081")
```

</details>

#### should stage the selected catalog through every Simple image tree builder

- should stage the selected catalog through every Simple image tree builder
- Inspect the shared 53-file SimpleOS font/legal projection
- Preserve every existing guest font registry path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should stage the selected catalog through every Simple image tree builder")
step("Inspect the shared 53-file SimpleOS font/legal projection")
expect_simpleos_font_asset()
step("Preserve every existing guest font registry path")
expect_simpleos_font_guest_paths()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/simpleos_font_asset_staging_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS pinned font asset staging.
- SimpleOS pinned font asset staging

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7a4dcf7ed1eef265de02a152afc697a41b269af23c242e7f34aa5070e298df8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a4dcf7ed1eef265de02a152afc697a41b269af23c242e7f34aa5070e298df8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a4dcf7ed1eef265de02a152afc697a41b269af23c242e7f34aa5070e298df8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/os/port/simpleos_font_asset_staging_spec.spl
mirror: doc/06_spec/02_integration/os/port/simpleos_font_asset_staging_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/port/simpleos_font_asset_staging_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/port/simpleos_font_asset_staging_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/port/simpleos_font_asset_staging_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/port/simpleos_font_asset_staging_spec.spl:209:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use the pinned Noto Sans Mono path length and hash' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/port/simpleos_font_asset_staging_spec.spl:209:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use the pinned Noto Sans Mono path length and hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/port/simpleos_font_asset_staging_spec.spl:218:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stage the selected catalog through every Simple image tree builder' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/port/simpleos_font_asset_staging_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should stage the selected catalog through every Simple image tree builder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
