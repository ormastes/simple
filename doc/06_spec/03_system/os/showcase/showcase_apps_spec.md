# showcase_apps_spec

> Launches each canonical showcase through every required surface. Acceptance

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# showcase_apps_spec

Launches each canonical showcase through every required surface. Acceptance

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/showcase/showcase_apps_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Launches each canonical showcase through every required surface. Acceptance
requires the real installed identity, process-owned window, nonblank rendered
frame, and a state or pixel change caused by production input routing.

The launch/evidence adapter is deliberately fail-fast until the standalone,
host-WM, and SimpleOS/QEMU wrappers expose correlated evidence. Source scans,
dummy frames, synthetic handles, and synthetic input cannot satisfy this spec.

## Scenarios

### Showcase applications on every launch surface

#### should run the 2D rendering showcase as a standalone app

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should run the 2D rendering showcase as a standalone app


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the 2D rendering showcase as a standalone app")
run_showcase_acceptance(GRAPHICS_2D, STANDALONE)
```

</details>

#### should run the 2D rendering showcase inside the host WM

- should run the 2D rendering showcase inside the host WM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the 2D rendering showcase inside the host WM")
run_showcase_acceptance(GRAPHICS_2D, HOST_WM)
```

</details>

#### should run the installed 2D rendering showcase inside SimpleOS WM

- should run the installed 2D rendering showcase inside SimpleOS WM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the installed 2D rendering showcase inside SimpleOS WM")
run_showcase_acceptance(GRAPHICS_2D, SIMPLEOS_WM)
```

</details>

#### should run the web standards showcase as a standalone app

- should run the web standards showcase as a standalone app


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the web standards showcase as a standalone app")
run_showcase_acceptance(WEB_STANDARDS, STANDALONE)
```

</details>

#### should run the web standards showcase inside the host WM

- should run the web standards showcase inside the host WM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the web standards showcase inside the host WM")
run_showcase_acceptance(WEB_STANDARDS, HOST_WM)
```

</details>

#### should run the installed web standards showcase inside SimpleOS WM

- should run the installed web standards showcase inside SimpleOS WM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the installed web standards showcase inside SimpleOS WM")
run_showcase_acceptance(WEB_STANDARDS, SIMPLEOS_WM)
```

</details>

#### should run the GUI widget showcase as a standalone app

- should run the GUI widget showcase as a standalone app


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the GUI widget showcase as a standalone app")
run_showcase_acceptance(GUI_WIDGETS, STANDALONE)
```

</details>

#### should run the GUI widget showcase inside the host WM

- should run the GUI widget showcase inside the host WM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the GUI widget showcase inside the host WM")
run_showcase_acceptance(GUI_WIDGETS, HOST_WM)
```

</details>

#### should run the installed GUI widget showcase inside SimpleOS WM

- should run the installed GUI widget showcase inside SimpleOS WM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the installed GUI widget showcase inside SimpleOS WM")
run_showcase_acceptance(GUI_WIDGETS, SIMPLEOS_WM)
```

</details>

### Showcase evidence rejects non-production substitutes

#### should reject source inspection without a launched surface

- should reject source inspection without a launched surface
- Submit source-only evidence without a live application
   - Expected: rejected_evidence_reason(true, false, false, false, false, true) equals `source-only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject source inspection without a launched surface")
step("Submit source-only evidence without a live application")
expect(rejected_evidence_reason(true, false, false, false, false, true)).to_equal("source-only")
```

</details>

#### should reject blank and unchanged framebuffer captures

- should reject blank and unchanged framebuffer captures
- Submit a blank framebuffer capture
   - Expected: rejected_evidence_reason(false, true, false, false, false, true) equals `blank-frame`
- Submit equal before and after framebuffer hashes
   - Expected: rejected_evidence_reason(false, false, false, false, false, false) equals `unchanged-frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject blank and unchanged framebuffer captures")
step("Submit a blank framebuffer capture")
expect(rejected_evidence_reason(false, true, false, false, false, true)).to_equal("blank-frame")
step("Submit equal before and after framebuffer hashes")
expect(rejected_evidence_reason(false, false, false, false, false, false)).to_equal("unchanged-frame")
```

</details>

#### should reject dummy renderers and synthetic backend handles

- should reject dummy renderers and synthetic backend handles
- Substitute a dummy renderer
   - Expected: rejected_evidence_reason(false, false, true, false, false, true) equals `dummy-renderer`
- Substitute a synthetic backend handle
   - Expected: rejected_evidence_reason(false, false, false, true, false, true) equals `synthetic-handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject dummy renderers and synthetic backend handles")
step("Substitute a dummy renderer")
expect(rejected_evidence_reason(false, false, true, false, false, true)).to_equal("dummy-renderer")
step("Substitute a synthetic backend handle")
expect(rejected_evidence_reason(false, false, false, true, false, true)).to_equal("synthetic-handle")
```

</details>

#### should reject synthetic input even when pixels differ

- should reject synthetic input even when pixels differ
- Mutate pixels through a synthetic event rather than the production input route
   - Expected: rejected_evidence_reason(false, false, false, false, true, true) equals `synthetic-input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject synthetic input even when pixels differ")
step("Mutate pixels through a synthetic event rather than the production input route")
expect(rejected_evidence_reason(false, false, false, false, true, true)).to_equal("synthetic-input")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SHOWCASE-001`
- `REQ-SHOWCASE-002`
- `REQ-SHOWCASE-003`
- `REQ-SHOWCASE-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a937ddb3dbc5f8d0d2b2ac2b3198351098ea650b3c499e5280bdcf7b7e0992e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a937ddb3dbc5f8d0d2b2ac2b3198351098ea650b3c499e5280bdcf7b7e0992e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a937ddb3dbc5f8d0d2b2ac2b3198351098ea650b3c499e5280bdcf7b7e0992e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/showcase/showcase_apps_spec.spl
mirror: doc/06_spec/03_system/os/showcase/showcase_apps_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/os/showcase/showcase_apps_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/showcase/showcase_apps_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/showcase/showcase_apps_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/showcase/showcase_apps_spec.spl:190:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run the 2D rendering showcase as a standalone app' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/showcase/showcase_apps_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should run the 2D rendering showcase as a standalone app' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/showcase/showcase_apps_spec.spl:195:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run the 2D rendering showcase inside the host WM' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/showcase/showcase_apps_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should run the 2D rendering showcase inside the host WM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/showcase/showcase_apps_spec.spl:200:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run the installed 2D rendering showcase inside SimpleOS WM' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/showcase/showcase_apps_spec.spl:200:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should run the installed 2D rendering showcase inside SimpleOS WM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/showcase/showcase_apps_spec.spl:205:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run the web standards showcase as a standalone app' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/showcase/showcase_apps_spec.spl:210:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run the web standards showcase inside the host WM' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/showcase/showcase_apps_spec.spl:215:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run the installed web standards showcase inside SimpleOS WM' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
