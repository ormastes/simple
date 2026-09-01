# Wine Proton Gate Specification

> Tests covering Wine Proton readiness gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Proton Gate Specification

## Scenarios

### Wine Proton readiness gate

#### lists Proton-specific runtime prerequisites above Wine

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists Proton-specific runtime prerequisites above Wine
   - Expected: required.len() equals `12`
   - Expected: required[0] equals `steam-runtime`
   - Expected: required[1] equals `pressure-vessel-container`
   - Expected: required[5] equals `vulkan-device`
   - Expected: required[6] equals `dxvk`
   - Expected: required[7] equals `vkd3d-proton`
   - Expected: required[11] equals `esync-or-fsync`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists Proton-specific runtime prerequisites above Wine")
val required = wine_proton_required_features()
expect(required.len()).to_equal(12)
expect(required[0]).to_equal("steam-runtime")
expect(required[1]).to_equal("pressure-vessel-container")
expect(required[5]).to_equal("vulkan-device")
expect(required[6]).to_equal("dxvk")
expect(required[7]).to_equal("vkd3d-proton")
expect(required[11]).to_equal("esync-or-fsync")
```

</details>

#### reports the first missing Proton feature

- reports the first missing Proton feature
   - Expected: state equals `missing-proton-launcher`
   - Expected: missing.len() equals `10`
   - Expected: missing[0] equals `proton-launcher`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing Proton feature")
val state = wine_proton_feature_gate("steam-runtime pressure-vessel-container")
expect(state).to_equal("missing-proton-launcher")
val missing = wine_proton_missing_features("steam-runtime pressure-vessel-container")
expect(missing.len()).to_equal(10)
expect(missing[0]).to_equal("proton-launcher")
```

</details>

#### keeps Proton blocked until full Wine readiness is verified

- keeps Proton blocked until full Wine readiness is verified
   - Expected: state equals `blocked-wine-blocked-missing-user32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Proton blocked until full Wine readiness is verified")
val state = wine_proton_readiness_gate(
    "process=verified exec_env=verified vm=verified renderer=verified",
    wine_proton_fixture_features()
)
expect(state).to_equal("blocked-wine-blocked-missing-user32")
```

</details>

#### keeps Proton blocked on missing graphics translation features

- keeps Proton blocked on missing graphics translation features
   - Expected: state equals `missing-vkd3d-proton`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Proton blocked on missing graphics translation features")
val features = "steam-runtime pressure-vessel-container proton-launcher wine-full " +
    "vulkan-loader vulkan-device dxvk steamworks-bridge controller-input shader-cache esync-or-fsync"
val state = wine_proton_readiness_gate(wine_proton_fixture_wine_gates(), features)
expect(state).to_equal("missing-vkd3d-proton")
```

</details>

#### allows Proton readiness only when Wine and Proton gates are complete

- allows Proton readiness only when Wine and Proton gates are complete
   - Expected: state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows Proton readiness only when Wine and Proton gates are complete")
val state = wine_proton_readiness_gate(wine_proton_fixture_wine_gates(), wine_proton_fixture_features())
expect(state).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_proton_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine Proton readiness gate.
- Wine Proton readiness gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `c2feab42e7391b5aaa134a96a07102e4caade7ffb9281369d497c57033eacdb0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2feab42e7391b5aaa134a96a07102e4caade7ffb9281369d497c57033eacdb0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2feab42e7391b5aaa134a96a07102e4caade7ffb9281369d497c57033eacdb0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_proton_gate_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_proton_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_proton_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_proton_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_proton_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_proton_gate_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists Proton-specific runtime prerequisites above Wine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_proton_gate_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing Proton feature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_proton_gate_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Proton blocked until full Wine readiness is verified' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
