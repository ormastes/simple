# WM Glass Theme on Host and SimpleOS

> Loads the selected Stitch-derived Aetheric package, renders a shared scene on

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM Glass Theme on Host and SimpleOS

Loads the selected Stitch-derived Aetheric package, renders a shared scene on

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Loads the selected Stitch-derived Aetheric package, renders a shared scene on
the production host and canonical SimpleOS desktop, and compares structured
theme/material/capability evidence with independently captured pixels.

The implementation helpers deliberately fail closed until backed by the
production theme bootstrap and canonical evidence wrappers. CSS text or a
screenshot alone cannot satisfy the scenarios.

## Scenarios

### Stitch glass theme on the production WM

#### should preserve one Aetheric glass material through host and canonical SimpleOS rendering

- should preserve one Aetheric glass material through host and canonical SimpleOS rendering
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve one Aetheric glass material through host and canonical SimpleOS rendering")
load_stitch_glass_theme()
render_hosted_wm_canonical()
apply_glass_css_and_widget_computed_styles()
boot_canonical_simpleos_desktop_qemu()
capture_and_compare_wm_glass_evidence()
require_wm_glass_theme_evidence()
```

</details>

<details>
<summary>Advanced: should preserve focus drag maximize restore text input and animated state changes</summary>

#### should preserve focus drag maximize restore text input and animated state changes

- should preserve focus drag maximize restore text input and animated state changes
- Drive focus pointer keyboard text and window-state interactions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve focus drag maximize restore text input and animated state changes")
render_hosted_wm_canonical()
step("Drive focus pointer keyboard text and window-state interactions")
capture_and_compare_wm_glass_evidence()
require_wm_glass_theme_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should preserve every required CSS glass property into computed style and Draw IR</summary>

#### should preserve every required CSS glass property into computed style and Draw IR

- should preserve every required CSS glass property into computed style and Draw IR
- Inspect variables RGBA gradients borders radii shadows backdrop effects typography and state selectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve every required CSS glass property into computed style and Draw IR")
apply_glass_css_and_widget_computed_styles()
step("Inspect variables RGBA gradients borders radii shadows backdrop effects typography and state selectors")
require_wm_glass_theme_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should use a named readable solid material when transparency is reduced or blur is unavailable</summary>

#### should use a named readable solid material when transparency is reduced or blur is unavailable

- should use a named readable solid material when transparency is reduced or blur is unavailable
- Enable reduced transparency and exercise an unavailable blur capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should use a named readable solid material when transparency is reduced or blur is unavailable")
step("Enable reduced transparency and exercise an unavailable blur capability")
capture_and_compare_wm_glass_evidence()
require_wm_glass_theme_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should reject corrupt identity unknown capability stale capture legacy entry and direct rendering</summary>

#### should reject corrupt identity unknown capability stale capture legacy entry and direct rendering

- should reject corrupt identity unknown capability stale capture legacy entry and direct rendering
- Substitute each forbidden identity capability capture entry and renderer case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject corrupt identity unknown capability stale capture legacy entry and direct rendering")
step("Substitute each forbidden identity capability capture entry and renderer case")
require_wm_glass_theme_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should retain deterministic performance provenance and stable semantic regions</summary>

#### should retain deterministic performance provenance and stable semantic regions

- should retain deterministic performance provenance and stable semantic regions
- Repeat semantic resolution and measure host QEMU frame latency and RSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain deterministic performance provenance and stable semantic regions")
step("Repeat semantic resolution and measure host QEMU frame latency and RSS")
capture_and_compare_wm_glass_evidence()
require_wm_glass_theme_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should reject fixture private raw-runtime and synthetic evidence routes</summary>

#### should reject fixture private raw-runtime and synthetic evidence routes

- should reject fixture private raw-runtime and synthetic evidence routes
- Audit every producer and evidence owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject fixture private raw-runtime and synthetic evidence routes")
step("Audit every producer and evidence owner")
require_wm_glass_theme_evidence()
```

</details>


</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `379ed563084698f37c86726834a5f58500077159a0e60daa7b202ea4571768fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `379ed563084698f37c86726834a5f58500077159a0e60daa7b202ea4571768fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `379ed563084698f37c86726834a5f58500077159a0e60daa7b202ea4571768fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl
mirror: doc/06_spec/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.md (current)
findings: 10 blockers: 2
  narrative=100 structure=70 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 10 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve one Aetheric glass material through host and canonical SimpleOS rendering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve focus drag maximize restore text input and animated state changes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve every required CSS glass property into computed style and Draw IR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use a named readable solid material when transparency is reduced or blur is unavailable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject corrupt identity unknown capability stale capture legacy entry and direct rendering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain deterministic performance provenance and stable semantic regions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
