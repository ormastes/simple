# Jupyter Kernel Install System Specification

> Tests covering Jupyter Kernel Installation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jupyter Kernel Install System Specification

## Scenarios

### Jupyter Kernel Installation

<details>
<summary>Advanced: should have kernel.json</summary>

#### should have kernel.json _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should have kernel.json
   - Expected: rt_file_exists("tools/jupyter/kernel.json") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have kernel.json")
expect(rt_file_exists("tools/jupyter/kernel.json")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have kernel_wrapper.py</summary>

#### should have kernel_wrapper.py _(slow)_

- should have kernel_wrapper.py
   - Expected: rt_file_exists("tools/jupyter/kernel_wrapper.py") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have kernel_wrapper.py")
expect(rt_file_exists("tools/jupyter/kernel_wrapper.py")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have install script</summary>

#### should have install script _(slow)_

- should have install script
   - Expected: rt_file_exists("tools/jupyter/install.shs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have install script")
expect(rt_file_exists("tools/jupyter/install.shs")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have valid kernel.json with Simple language</summary>

#### should have valid kernel.json with Simple language _(slow)_

- should have valid kernel.json with Simple language


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have valid kernel.json with Simple language")
val content = rt_file_read_text("tools/jupyter/kernel.json") ?? ""
expect(content).to_contain("Simple")
expect(content).to_contain("simple")
expect(content).to_contain(".spl")
```

</details>


</details>

<details>
<summary>Advanced: should have kernel main entry point</summary>

#### should have kernel main entry point _(slow)_

- should have kernel main entry point
   - Expected: rt_file_exists("src/app/jupyter_kernel/main.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have kernel main entry point")
expect(rt_file_exists("src/app/jupyter_kernel/main.spl")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have kernel protocol module</summary>

#### should have kernel protocol module _(slow)_

- should have kernel protocol module
   - Expected: rt_file_exists("src/app/jupyter_kernel/protocol.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have kernel protocol module")
expect(rt_file_exists("src/app/jupyter_kernel/protocol.spl")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have kernel session module</summary>

#### should have kernel session module _(slow)_

- should have kernel session module
   - Expected: rt_file_exists("src/app/jupyter_kernel/session.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should have kernel session module")
expect(rt_file_exists("src/app/jupyter_kernel/session.spl")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Jupyter Kernel Installation.
- Jupyter Kernel Installation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
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

- Canonical SPipe generation for source `ca74fc0aa8d3326d1fa9958181c4a926f4a4327e9d4eb7775b2ead4d2f3cacfd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca74fc0aa8d3326d1fa9958181c4a926f4a4327e9d4eb7775b2ead4d2f3cacfd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca74fc0aa8d3326d1fa9958181c4a926f4a4327e9d4eb7775b2ead4d2f3cacfd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl
mirror: doc/06_spec/03_system/tools/jupyter/jupyter_kernel_install_system_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/jupyter/jupyter_kernel_install_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/jupyter/jupyter_kernel_install_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have kernel.json' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should have kernel.json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have kernel_wrapper.py' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should have kernel_wrapper.py' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have install script' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should have install script' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have valid kernel.json with Simple language' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have kernel main entry point' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have kernel protocol module' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
