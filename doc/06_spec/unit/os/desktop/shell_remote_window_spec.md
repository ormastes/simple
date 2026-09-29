# @manual: primary

> Purpose: Prove that DesktopShell remote windows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that DesktopShell remote windows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/desktop/shell_remote_window_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that DesktopShell remote windows.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-DESKTOP-001
doc/01_research/local/REQ-OS-DESKTOP-001.md
doc/03_plan/sys_test/REQ-OS-DESKTOP-001.md
doc/04_architecture/REQ-OS-DESKTOP-001.md
doc/05_design/REQ-OS-DESKTOP-001.md

## Scenarios

### DesktopShell remote windows

#### resolves remote create-window identity from launcher process metadata

- Verify: resolves remote create-window identity from launcher process metadata
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: shell.compositor.window_owner_port(wid) equals `91`
   - Expected: shell.compositor.window_process_id(wid) equals `4101`
   - Expected: shell.compositor.window_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: shell.wm.window_owner_process_id(wid) equals `4101`
   - Expected: shell.wm.window_owner_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_app_id_for_pid(4101) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_window_count(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: resolves remote create-window identity from launcher process metadata")
launcher_init()
expect(launcher_record_process(4101, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", 4101, 91))

expect(shell.compositor.window_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val ids = shell.compositor.windows_for_process(4101)
expect(ids.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val wid = ids[0]
expect(shell.compositor.window_owner_port(wid)).to_equal(91)  # oracle: 91 — named expected value from the requirement
expect(shell.compositor.window_process_id(wid)).to_equal(4101)  # oracle: 4101 — named expected value from the requirement
expect(shell.compositor.window_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(shell.wm.window_owner_process_id(wid)).to_equal(4101)  # oracle: 4101 — named expected value from the requirement
expect(shell.wm.window_owner_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_app_id_for_pid(4101)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_window_count(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### groups multiple remote windows under one manifest app_id and unwinds on destroy

- Verify: groups multiple remote windows under one manifest app_id and unwinds on destroy
   - Expected: shell.compositor.window_count() equals `2`
   - Expected: shell.compositor.window_count_for_process(5202) equals `2`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_count_for_process(5202) equals `2`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: launcher_get_process_window_count(0) equals `2`
   - Expected: ids.len() equals `2`
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `1`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `1`
   - Expected: launcher_get_process_window_count(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: groups multiple remote windows under one manifest app_id and unwinds on destroy")
launcher_init()
expect(launcher_record_process(5202, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", 5202, 101))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", 5202, 102))

expect(shell.compositor.window_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(shell.compositor.window_count_for_process(5202)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_count_for_process(5202)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(launcher_get_process_window_count(0)).to_equal(2)  # oracle: 2 — named expected value from the requirement

val ids = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement

shell.apply_wm_action(WmAction(
    kind: "destroy_window",
    window_id: ids[0],
    title: "",
    x: 0,
    y: 0,
    width: 0,
    height: 0,
    content: "",
    process_id: 0,
    app_id: "",
    owner_port: 0,
    src_port: 101
))

expect(shell.compositor.window_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)
expect(launcher_get_process_window_count(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reaps crashed remote windows via the dead-process reconcile path

- Verify: reaps crashed remote windows via the dead-process reconcile path
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: shell.wm.window_count_for_process(6303) equals `1`
   - Expected: launcher_get_process_state(0) equals `crashed`
   - Expected: launcher_get_running_process_count() equals `0`
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(6303) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: reaps crashed remote windows via the dead-process reconcile path")
launcher_init()
expect(launcher_record_process(6303, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", 6303, 201))
expect(shell.compositor.window_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(shell.wm.window_count_for_process(6303)).to_equal(1)  # oracle: 1 — named expected value from the requirement

# Simulate an unexpected process death (nonzero exit).
launcher_note_task_probe(6303, false, 137)
expect(launcher_get_process_state(0)).to_equal("crashed")
expect(launcher_get_running_process_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(shell.wm.window_count_for_process(6303)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reaps graceful exits on reconcile without misclassifying as crashes

- Verify: reaps graceful exits on reconcile without misclassifying as crashes
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: launcher_get_process_state(0) equals `exited`
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(6404) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: reaps graceful exits on reconcile without misclassifying as crashes")
launcher_init()
expect(launcher_record_process(6404, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", 6404, 202))
expect(shell.compositor.window_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement

launcher_note_task_probe(6404, false, 0)
expect(launcher_get_process_state(0)).to_equal("exited")

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(shell.wm.window_count_for_process(6404)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-OS-DESKTOP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e26783bf92a4c59419bc639b90851ffb046695bae0b67a8b27d647e8f5afa01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e26783bf92a4c59419bc639b90851ffb046695bae0b67a8b27d647e8f5afa01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e26783bf92a4c59419bc639b90851ffb046695bae0b67a8b27d647e8f5afa01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/desktop/shell_remote_window_spec.spl
mirror: doc/06_spec/unit/os/desktop/shell_remote_window_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/os/desktop/shell_remote_window_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/desktop/shell_remote_window_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/desktop/shell_remote_window_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/desktop/shell_remote_window_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/os/desktop/shell_remote_window_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves remote create-window identity from launcher process metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/desktop/shell_remote_window_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups multiple remote windows under one manifest app_id and unwinds on destroy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/desktop/shell_remote_window_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaps crashed remote windows via the dead-process reconcile path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
