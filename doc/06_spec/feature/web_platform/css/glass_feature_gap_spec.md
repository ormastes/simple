# Glass Feature Gap Specification

> Tests covering Glass comparison feature gap detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Feature Gap Specification

## Scenarios

### Glass comparison feature gap detection

#### does not report supported before and after pseudo-elements as missing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not report supported before and after pseudo-elements as missing
   - Expected: _contains(missing, "pseudo-elements (::before/::after)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not report supported before and after pseudo-elements as missing")
val html = "<style>.card::before { content: 'A'; } .card::after { content: 'B'; }</style><div class='card'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "pseudo-elements (::before/::after)")).to_equal(false)
```

</details>

#### still reports unsupported glass effect features

- still reports unsupported glass effect features
   - Expected: _contains(missing, "backdrop-filter: blur()") is true
   - Expected: _contains(missing, "box-shadow (multi-layer)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("still reports unsupported glass effect features")
val html = "<style>.panel { backdrop-filter: blur(12px); box-shadow: 0 8px 24px #000; }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "backdrop-filter: blur()")).to_equal(true)
expect(_contains(missing, "box-shadow (multi-layer)")).to_equal(false)
```

</details>

#### does not report multi-layer box shadow as unsupported

- does not report multi-layer box shadow as unsupported
   - Expected: _contains(missing, "box-shadow (multi-layer)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not report multi-layer box shadow as unsupported")
val html = "<style>.panel { box-shadow: 0 8px 24px #000, 0 2px 6px #333; }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "box-shadow (multi-layer)")).to_equal(false)
```

</details>

#### does not report linear gradients as unsupported

- does not report linear gradients as unsupported
   - Expected: _contains(missing, "linear-gradient()") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not report linear gradients as unsupported")
val html = "<style>.panel { background: linear-gradient(180deg, #fff, #000); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "linear-gradient()")).to_equal(false)
```

</details>

#### does not report simple translate transforms as unsupported

- does not report simple translate transforms as unsupported
   - Expected: _contains(missing, "transform") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not report simple translate transforms as unsupported")
val html = "<style>.panel { transform: translate(4px, 4px); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(false)
```

</details>

#### still reports unsupported transform functions

- still reports unsupported transform functions
   - Expected: _contains(missing, "transform") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("still reports unsupported transform functions")
val html = "<style>.panel { transform: rotate(5deg); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(true)
```

</details>

#### still reports multi-function translate transforms as partial

- still reports multi-function translate transforms as partial
   - Expected: _contains(missing, "transform") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("still reports multi-function translate transforms as partial")
val html = "<style>.panel { transform: translate(4px, 4px) translateX(2px); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(true)
```

</details>

#### does not report simple percentage translate transforms as unsupported

- does not report simple percentage translate transforms as unsupported
   - Expected: _contains(missing, "transform") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not report simple percentage translate transforms as unsupported")
val html = "<style>.panel { transform: translate(50%, 0); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(false)
```

</details>

#### still reports translate transforms with unsupported units

- still reports translate transforms with unsupported units
   - Expected: _contains(missing, "transform") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("still reports translate transforms with unsupported units")
val html = "<style>.panel { transform: translate(2em, 0); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/glass_feature_gap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Glass comparison feature gap detection.
- Glass comparison feature gap detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f71f1beb2d6dca23d99922c1622944dc9ba49bab5e73843edc52a8cf732b3253`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f71f1beb2d6dca23d99922c1622944dc9ba49bab5e73843edc52a8cf732b3253`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f71f1beb2d6dca23d99922c1622944dc9ba49bab5e73843edc52a8cf732b3253`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/web_platform/css/glass_feature_gap_spec.spl
mirror: doc/06_spec/feature/web_platform/css/glass_feature_gap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/glass_feature_gap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/glass_feature_gap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/glass_feature_gap_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not report supported before and after pseudo-elements as missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/glass_feature_gap_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still reports unsupported glass effect features' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/glass_feature_gap_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not report multi-layer box shadow as unsupported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
