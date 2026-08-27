# Hosted Entry Live Proof Focus Contract Specification

> Tests covering hosted WM live-proof focus contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Entry Live Proof Focus Contract Specification

## Scenarios

### hosted WM live-proof focus contract

#### seeds an unfocused peer before the focused Terminal window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- seeds an unfocused peer before the focused Terminal window


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("seeds an unfocused peer before the focused Terminal window")
val source = file_read("src/os/hosted/hosted_entry.spl")
val lifecycle = file_read("src/os/compositor/wm_action_lifecycle.spl")
val seed_start = source.find("fn _seed_live_proof_surface")
val seed_end = source.find("fn _physical_surface_geometry")
expect(seed_start).to_be_greater_than(-1)
expect(seed_end).to_be_greater_than(seed_start)
val seed = source.substring(seed_start, seed_end)
val files = seed.find("\"Files\"")
val terminal = seed.find("\"Terminal\"")
expect(files).to_be_greater_than(-1)
expect(terminal).to_be_greater_than(files)
expect(seed).to_contain("\"files\"")
expect(seed).to_contain("\"terminal\"")
val create_start = lifecycle.find("if action.kind == \"create_window\" or action.kind == \"create_web_window\":")
val create_end = lifecycle.find("if action.kind == \"destroy_window\":")
expect(create_start).to_be_greater_than(-1)
expect(create_end).to_be_greater_than(create_start)
val create = lifecycle.substring(create_start, create_end)
expect(create).to_contain("focused: true")
expect(create).to_contain("out_windows = wm_lifecycle_focus_window(out_windows, id)")
```

</details>

#### keeps the normal shared MDI seed outside live-proof mode

- keeps the normal shared MDI seed outside live-proof mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps the normal shared MDI seed outside live-proof mode")
val source = file_read("src/os/hosted/hosted_entry.spl")
val run_start = source.find("fn _run_hosted_wm")
expect(run_start).to_be_greater_than(-1)
val run = source.substring(run_start, source.len())
val proof_seed = run.find("comp = _seed_live_proof_surface(comp)")
val normal_seed = run.find("comp = _seed_host_compositor_shared_mdi(comp)")
expect(proof_seed).to_be_greater_than(-1)
expect(normal_seed).to_be_greater_than(proof_seed)
```

</details>

#### routes native Tab through the canonical next-window focus operation

- routes native Tab through the canonical next-window focus operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes native Tab through the canonical next-window focus operation")
val entry = file_read("src/os/hosted/hosted_entry.spl")
val core = file_read("src/os/compositor/host_compositor_core.spl")
val cycle_start = core.find("fn host_compositor_cycle_focus")
val cycle_end = core.find("fn host_compositor_focused_window_id")
expect(entry).to_contain("elif keycode == KEY_TAB:")
expect(entry).to_contain("comp = host_compositor_cycle_focus(comp)")
expect(cycle_start).to_be_greater_than(-1)
expect(cycle_end).to_be_greater_than(cycle_start)
val cycle = core.substring(cycle_start, cycle_end)
expect(cycle).to_contain("var next_idx = focused_idx + 1")
expect(cycle).to_contain("out.focus_window(out.windows[next_idx].id)")
```

</details>

#### restores only the focused window changed by the evidence maximize command

- restores only the focused window changed by the evidence maximize command
   - Expected: restore.find("host_compositor_restore_all") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("restores only the focused window changed by the evidence maximize command")
val source = file_read("src/os/hosted/hosted_entry.spl")
val restore_start = source.find("elif command.action == \"restore\":")
val restore_end = source.find("elif command.action == \"close\":")
expect(restore_start).to_be_greater_than(-1)
expect(restore_end).to_be_greater_than(restore_start)
val restore = source.substring(restore_start, restore_end)
expect(restore).to_contain("val focused = host_compositor_focused_window_id(comp)")
expect(restore).to_contain("if focused > 0: comp.restore_window(focused)")
expect(restore.find("host_compositor_restore_all")).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted WM live-proof focus contract.
- hosted WM live-proof focus contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db72a317615e2d3cd6a25fb1119aed274c3c3fa825fe680e91b54be056cbb499`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db72a317615e2d3cd6a25fb1119aed274c3c3fa825fe680e91b54be056cbb499`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db72a317615e2d3cd6a25fb1119aed274c3c3fa825fe680e91b54be056cbb499`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl
mirror: doc/06_spec/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seeds an unfocused peer before the focused Terminal window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the normal shared MDI seed outside live-proof mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes native Tab through the canonical next-window focus operation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
