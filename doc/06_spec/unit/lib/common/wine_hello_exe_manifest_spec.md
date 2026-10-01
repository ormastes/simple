# Wine Hello Exe Manifest Specification

> Tests covering Wine hello.exe manifest and VM probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Hello Exe Manifest Specification

## Scenarios

### Wine hello.exe manifest and VM probe

#### requires the composed precondition manifest on the manifest probe path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires the composed precondition manifest on the manifest probe path
   - Expected: result.status equals `executed`
   - Expected: wine_hello_exe_manifest_can_execute(wine_known_hello_exe_fixture_bytes(), manifest, wine_hello_fixture_verified_gates()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the composed precondition manifest on the manifest probe path")
val manifest = _ready_manifest()
val result = wine_hello_exe_probe_manifest(wine_known_hello_exe_fixture_bytes(), manifest, wine_hello_fixture_verified_gates())
expect(result.status).to_equal("executed")
expect(wine_hello_exe_manifest_can_execute(wine_known_hello_exe_fixture_bytes(), manifest, wine_hello_fixture_verified_gates())).to_equal(true)
```

</details>

#### accepts structured execution evidence on the manifest probe path

- accepts structured execution evidence on the manifest probe path
   - Expected: result.status equals `executed`
   - Expected: wine_hello_exe_manifest_evidence_can_execute(wine_known_hello_exe_fixture_bytes(), manifest, evidence) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts structured execution evidence on the manifest probe path")
val manifest = _ready_manifest()
val evidence = wine_cpu_execution_evidence_all_ready()
val result = wine_hello_exe_probe_manifest_evidence(wine_known_hello_exe_fixture_bytes(), manifest, evidence)
expect(result.status).to_equal("executed")
expect(wine_hello_exe_manifest_evidence_can_execute(wine_known_hello_exe_fixture_bytes(), manifest, evidence)).to_equal(true)
```

</details>

#### executes only after the PE image is mapped into an OS-backed VM process

- executes only after the PE image is mapped into an OS-backed VM process
   - Expected: result.status equals `executed`
   - Expected: result.stdout equals `Hello from SimpleOS Wine\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes only after the PE image is mapped into an OS-backed VM process")
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_hello_exe_probe_vm(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates(), space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### blocks the VM probe when process/container evidence is only modeled

- blocks the VM probe when process/container evidence is only modeled
   - Expected: result.status equals `blocked`
   - Expected: result.error equals `missing-os-process`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks the VM probe when process/container evidence is only modeled")
val space = wine_vm_process_space_new(0, 0, "")
val result = wine_hello_exe_probe_vm(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates(), space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("missing-os-process")
```

</details>

#### executes the manifest path through OS-backed VM mapping

- executes the manifest path through OS-backed VM mapping
   - Expected: result.status equals `executed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes the manifest path through OS-backed VM mapping")
val manifest = _ready_manifest()
val evidence = wine_cpu_execution_evidence_all_ready()
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_hello_exe_probe_manifest_evidence_vm(wine_known_hello_exe_fixture_bytes(), manifest, evidence, space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.status).to_equal("executed")
```

</details>

#### blocks the manifest probe before PE parsing when process evidence is incomplete

- blocks the manifest probe before PE parsing when process evidence is incomplete
   - Expected: result.status equals `blocked`
   - Expected: result.error equals `blocked-process:insufficient-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks the manifest probe before PE parsing when process evidence is incomplete")
val manifest = wine_precondition_manifest("[desktop-e2e] process-backed:ok app=browser_demo pid=1", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
val result = wine_hello_exe_probe_manifest(wine_known_hello_exe_fixture_bytes(), manifest, wine_hello_fixture_verified_gates())
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("blocked-process:insufficient-evidence")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_hello_exe_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine hello.exe manifest and VM probe.
- Wine hello.exe manifest and VM probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `17a69a1023c79301ff385a393b2435c61eeb9aaaa47728b731b2c2fbdbc51fbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17a69a1023c79301ff385a393b2435c61eeb9aaaa47728b731b2c2fbdbc51fbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17a69a1023c79301ff385a393b2435c61eeb9aaaa47728b731b2c2fbdbc51fbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/wine_hello_exe_manifest_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_hello_exe_manifest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_hello_exe_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_hello_exe_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_hello_exe_manifest_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the composed precondition manifest on the manifest probe path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_hello_exe_manifest_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes only after the PE image is mapped into an OS-backed VM process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_hello_exe_manifest_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks the VM probe when process/container evidence is only modeled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
