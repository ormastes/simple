# Ipc Surface Specification

> Tests covering IPC surface state, IPC surface changes, IPC subscribe command.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Surface Specification

## Scenarios

### IPC surface state

#### reports surface count in state response

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports surface count in state response


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports surface count in state response")
val root = text_widget("ipc_surf_root", "Main")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "surface_count"
```

</details>

#### reflects multiple surfaces

- reflects multiple surfaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reflects multiple surfaces")
val root = text_widget("ipc_surf_multi_root", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val popup_root = text_widget("ipc_surf_popup_r", "Popup")
val popup_tree = UITree.new(popup_root)
session.open_surface("popup", popup_tree)
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "surface_count"
```

</details>

#### reports viewport in state response

- reports viewport in state response


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports viewport in state response")
val root = text_widget("ipc_surf_vp_root", "VP")
val tree = UITree.new(root)
var session = new_session(tree)
session.set_viewport(120, 40, "cli")
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "120x40"
```

</details>

### IPC surface changes

#### captures changes from tree update

- captures changes from tree update


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures changes from tree update")
val root1 = column("ipc_chg_root", [
    text_widget("ipc_chg_t1", "V1")
])
val tree1 = UITree.new(root1)
var session = new_session(tree1)
val root2 = column("ipc_chg_root", [
    text_widget("ipc_chg_t1", "V1"),
    text_widget("ipc_chg_t2", "V2")
])
val tree2 = UITree.new(root2)
session.update_tree(tree2)
val response = process_command(session, "{\"command\": \"get_changes\", \"count\": 10}")
expect response to_contain "changes"
```

</details>

### IPC subscribe command

#### returns initial state on subscribe

- returns initial state on subscribe


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns initial state on subscribe")
val root = text_widget("ipc_sub_root", "Sub")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"subscribe\"}")
expect response to_contain "mode"
expect response to_contain "NORMAL"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/ipc_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering IPC surface state, IPC surface changes, IPC subscribe command.
- IPC surface state
- IPC surface changes
- IPC subscribe command

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

- Canonical SPipe generation for source `76c5b7a168b67d8f4845b3d6adc4df1d028b90d370ebfc5888d6edf06e5dad7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76c5b7a168b67d8f4845b3d6adc4df1d028b90d370ebfc5888d6edf06e5dad7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76c5b7a168b67d8f4845b3d6adc4df1d028b90d370ebfc5888d6edf06e5dad7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/ipc_surface_spec.spl
mirror: doc/06_spec/unit/app/ui/ipc_surface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/ipc_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/ipc_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/ipc_surface_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports surface count in state response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ipc_surface_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects multiple surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ipc_surface_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports viewport in state response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
