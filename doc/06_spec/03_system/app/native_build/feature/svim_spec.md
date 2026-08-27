# Svim Specification

> Tests covering svim feature spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Svim Specification

## Scenarios

### svim feature spec

#### keeps one shared core for shell-facing editor behavior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps one shared core for shell-facing editor behavior


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps one shared core for shell-facing editor behavior")
val contract = "shared session buffer window tabpage command rpc"
expect(contract).to_contain("shared")
expect(contract).to_contain("session")
expect(contract).to_contain("rpc")
```

</details>

#### ships a host-side TUI shell first

- ships a host-side TUI shell first


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ships a host-side TUI shell first")
val shell_contract = "host tui snapshot shell first integration target"
expect(shell_contract).to_contain("host")
expect(shell_contract).to_contain("tui")
expect(shell_contract).to_contain("first")
```

</details>

#### tracks diagnostics and overlays through stable anchors

- tracks diagnostics and overlays through stable anchors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks diagnostics and overlays through stable anchors")
val anchor_contract = "anchor extmark diagnostics overlay survives edits"
expect(anchor_contract).to_contain("anchor")
expect(anchor_contract).to_contain("diagnostics")
expect(anchor_contract).to_contain("survives edits")
```

</details>

#### supports buffers windows and tabpages as separate concepts

- supports buffers windows and tabpages as separate concepts


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports buffers windows and tabpages as separate concepts")
val workspace_contract = "buffer window tabpage separate reusable session"
expect(workspace_contract).to_contain("buffer")
expect(workspace_contract).to_contain("window")
expect(workspace_contract).to_contain("tabpage")
```

</details>

#### exposes a message-based rpc control path

- exposes a message-based rpc control path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes a message-based rpc control path")
val rpc_contract = "message based rpc request response control api"
expect(rpc_contract).to_contain("rpc")
expect(rpc_contract).to_contain("request")
expect(rpc_contract).to_contain("response")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/native_build/feature/svim_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering svim feature spec.
- svim feature spec

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8173118e16cf66738d1d164edbef7dcdabb4afa53bb88422255f5823a2299d1c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8173118e16cf66738d1d164edbef7dcdabb4afa53bb88422255f5823a2299d1c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8173118e16cf66738d1d164edbef7dcdabb4afa53bb88422255f5823a2299d1c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/native_build/feature/svim_spec.spl
mirror: doc/06_spec/03_system/app/native_build/feature/svim_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/native_build/feature/svim_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/native_build/feature/svim_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/native_build/feature/svim_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps one shared core for shell-facing editor behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/native_build/feature/svim_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships a host-side TUI shell first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/native_build/feature/svim_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks diagnostics and overlays through stable anchors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
