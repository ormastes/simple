# Wine Precondition Manifest Specification

> Tests covering Wine precondition manifest.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Precondition Manifest Specification

## Scenarios

### Wine precondition manifest

#### blocks on incomplete process-backed app evidence before proxy gates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocks on incomplete process-backed app evidence before proxy gates
   - Expected: manifest.ready is false
   - Expected: manifest.state equals `blocked-process:insufficient-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks on incomplete process-backed app evidence before proxy gates")
val partial_log = "[desktop-e2e] process-backed:ok app=browser_demo pid=1\n" +
    "[desktop-e2e] process-backed:ok app=hello_world pid=2\n" +
    "[desktop-e2e] process-backed:ok app=editor pid=3"
val manifest = wine_precondition_manifest(partial_log, "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-process:insufficient-evidence")
```

</details>

#### reports the first ordered precondition blocker

- reports the first ordered precondition blocker
   - Expected: manifest.ready is false
   - Expected: manifest.state equals `blocked-vm:missing-mprotect`
   - Expected: manifest.gates equals `process=verified exec_env=verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first ordered precondition blocker")
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "missing-mprotect", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-vm:missing-mprotect")
expect(manifest.gates).to_equal("process=verified exec_env=verified")
```

</details>

#### requires the SimpleOS VM/container executable environment before VM adapter gates

- requires the SimpleOS VM/container executable environment before VM adapter gates
   - Expected: manifest.ready is false
   - Expected: manifest.state equals `blocked-exec-env:missing-simpleos-container-namespace`
   - Expected: manifest.gates equals `process=verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the SimpleOS VM/container executable environment before VM adapter gates")
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "missing-simpleos-container-namespace", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-exec-env:missing-simpleos-container-namespace")
expect(manifest.gates).to_equal("process=verified")
```

</details>

#### keeps renderer readiness separate from hello.exe substrate gates

- keeps renderer readiness separate from hello.exe substrate gates
   - Expected: manifest.ready is false
   - Expected: manifest.state equals `blocked-renderer:missing-clipboard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps renderer readiness separate from hello.exe substrate gates")
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "ready", "missing-clipboard", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-renderer:missing-clipboard")
expect(manifest.gates).to_contain("vm=verified")
```

</details>

#### requires host, POSIX, pthread, dynload, async, and PE gates before hello.exe

- requires host, POSIX, pthread, dynload, async, and PE gates before hello.exe
   - Expected: manifest.ready is false
   - Expected: manifest.state equals `blocked-async:missing-submit-write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires host, POSIX, pthread, dynload, async, and PE gates before hello.exe")
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "ready", "ready", "ready", "ready", "ready", "ready", "missing-submit-write", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-async:missing-submit-write")
expect(manifest.gates).to_contain("dynload=verified")
```

</details>

#### requires the modeled NT bridge before hello.exe

- requires the modeled NT bridge before hello.exe
   - Expected: manifest.ready is false
   - Expected: manifest.state equals `blocked-nt-bridge:missing-heap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the modeled NT bridge before hello.exe")
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "missing-heap")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-nt-bridge:missing-heap")
expect(manifest.gates).to_contain("pe_loader=verified")
```

</details>

#### emits the verified gate string accepted by the hello.exe gate

- emits the verified gate string accepted by the hello.exe gate
   - Expected: manifest.ready is true
   - Expected: manifest.state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the verified gate string accepted by the hello.exe gate")
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(true)
expect(manifest.state).to_equal("ready")
expect(manifest.gates).to_contain("process=verified")
expect(manifest.gates).to_contain("exec_env=verified")
expect(manifest.gates).to_contain("pe_loader=verified")
expect(manifest.gates).to_contain("nt_bridge=verified")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_precondition_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine precondition manifest.
- Wine precondition manifest

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

- Canonical SPipe generation for source `e307b7f89c76ed0870f753fe182be5c7995e4f1e691894f90acf49e617f0b68b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e307b7f89c76ed0870f753fe182be5c7995e4f1e691894f90acf49e617f0b68b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e307b7f89c76ed0870f753fe182be5c7995e4f1e691894f90acf49e617f0b68b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/wine_precondition_manifest_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_precondition_manifest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_precondition_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_precondition_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_precondition_manifest_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks on incomplete process-backed app evidence before proxy gates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_precondition_manifest_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first ordered precondition blocker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_precondition_manifest_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the SimpleOS VM/container executable environment before VM adapter gates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
