# Wine Image Map Specification

> Tests covering Wine image map gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Image Map Specification

## Scenarios

### Wine image map gate

#### requires an entry point

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires an entry point
   - Expected: wine_image_map_gate(_minimal_image(0, 0x5000)) equals `missing-entrypoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires an entry point")
expect(wine_image_map_gate(_minimal_image(0, 0x5000))).to_equal("missing-entrypoint")
```

</details>

#### requires the entry point to map through a section

- requires the entry point to map through a section
   - Expected: wine_image_map_gate(_minimal_image(0x9000, 0x5000)) equals `entrypoint-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the entry point to map through a section")
expect(wine_image_map_gate(_minimal_image(0x9000, 0x5000))).to_equal("entrypoint-unmapped")
```

</details>

#### requires an image larger than headers

- requires an image larger than headers
   - Expected: wine_image_map_gate(_minimal_image(0x2010, 0x100)) equals `bad-image-size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires an image larger than headers")
expect(wine_image_map_gate(_minimal_image(0x2010, 0x100))).to_equal("bad-image-size")
```

</details>

#### rejects section raw data outside the PE bytes

- rejects section raw data outside the PE bytes
   - Expected: wine_image_map_gate(_minimal_image_with_raw_overflow(0x2010, 0x5000)) equals `section-raw-out-of-bounds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects section raw data outside the PE bytes")
expect(wine_image_map_gate(_minimal_image_with_raw_overflow(0x2010, 0x5000))).to_equal("section-raw-out-of-bounds")
```

</details>

#### requires the entry point section to be executable

- requires the entry point section to be executable
   - Expected: wine_image_map_gate(_minimal_image_without_executable_section(0x2010, 0x5000)) equals `entry-section-not-executable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the entry point section to be executable")
expect(wine_image_map_gate(_minimal_image_without_executable_section(0x2010, 0x5000))).to_equal("entry-section-not-executable")
```

</details>

#### accepts a bounded mapped image layout

- accepts a bounded mapped image layout
   - Expected: wine_image_map_gate(_minimal_image(0x2010, 0x5000)) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a bounded mapped image layout")
expect(wine_image_map_gate(_minimal_image(0x2010, 0x5000))).to_equal("ready")
```

</details>

#### requires the entry execution window to stay mapped and contiguous

- requires the entry execution window to stay mapped and contiguous
   - Expected: wine_image_entry_window_gate(_minimal_image(0x2010, 0x5000), 27) equals `ready`
   - Expected: wine_image_entry_window_gate(_minimal_image(0x2010, 0x5000), 0) equals `invalid-entry-window`
   - Expected: wine_image_entry_window_gate(_minimal_image(0x21f0, 0x5000), 32) equals `entry-window-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the entry execution window to stay mapped and contiguous")
expect(wine_image_entry_window_gate(_minimal_image(0x2010, 0x5000), 27)).to_equal("ready")
expect(wine_image_entry_window_gate(_minimal_image(0x2010, 0x5000), 0)).to_equal("invalid-entry-window")
expect(wine_image_entry_window_gate(_minimal_image(0x21f0, 0x5000), 32)).to_equal("entry-window-unmapped")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_image_map_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine image map gate.
- Wine image map gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `385830fc0e843e79126aa089c2f4e9f42952f2354aa4a299143e6e4cf309b7a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `385830fc0e843e79126aa089c2f4e9f42952f2354aa4a299143e6e4cf309b7a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `385830fc0e843e79126aa089c2f4e9f42952f2354aa4a299143e6e4cf309b7a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/wine_image_map_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_image_map_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_image_map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_image_map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_image_map_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires an entry point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_image_map_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the entry point to map through a section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_image_map_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires an image larger than headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
