# Browser Demo Launcher Lifecycle Specification

> Tests covering Browser Demo launcher lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Demo Launcher Lifecycle Specification

## Scenarios

### Browser Demo launcher lifecycle

#### exposes the built-in browser_demo manifest identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes the built-in browser_demo manifest identity
   - Expected: launcher_get_app_path(5) equals `/sys/apps/browser_demo.smf`
   - Expected: launcher_get_app_identity(5) equals `/sys/apps/browser_demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the built-in browser_demo manifest identity")
launcher_init()
expect(launcher_get_app_path(5)).to_equal("/sys/apps/browser_demo.smf")
expect(launcher_get_app_identity(5)).to_equal("/sys/apps/browser_demo")
```

</details>

#### groups two remote windows under one launcher-owned app_id

- groups two remote windows under one launcher-owned app_id
   - Expected: shell.compositor.window_count() equals `2`
   - Expected: shell.compositor.window_count_for_process(pid) equals `2`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_count_for_process(pid) equals `2`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/browser_demo`
   - Expected: launcher_get_process_window_count(0) equals `2`
   - Expected: launcher_get_app_window_count(5) equals `2`
   - Expected: launcher_get_app_launch_state(5) equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("groups two remote windows under one launcher-owned app_id")
launcher_init()
val pid: u64 = 8301
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 401))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 402))

expect(shell.compositor.window_count()).to_equal(2)
expect(shell.compositor.window_count_for_process(pid)).to_equal(2)
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_count_for_process(pid)).to_equal(2)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/browser_demo")
expect(launcher_get_process_window_count(0)).to_equal(2)
expect(launcher_get_app_window_count(5)).to_equal(2)
expect(launcher_get_app_launch_state(5)).to_equal("running")
```

</details>

#### keeps grouping stable after a title change on one window

- keeps grouping stable after a title change on one window
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: ids_before.len() equals `2`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_owner_app_id(first_wid) equals `/sys/apps/browser_demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps grouping stable after a title change on one window")
launcher_init()
val pid: u64 = 8402
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 411))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 412))
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)

val ids_before = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids_before.len()).to_equal(2)
val first_wid = ids_before[0]

shell.apply_wm_action(WmAction(
    kind: "update_title",
    window_id: first_wid,
    title: "Browser Demo — new-tab.simple",
    x: 0,
    y: 0,
    width: 0,
    height: 0,
    content: "",
    process_id: 0,
    app_id: "",
    owner_port: 0,
    src_port: 411
))

expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_owner_app_id(first_wid)).to_equal("/sys/apps/browser_demo")
```

</details>

#### destroys one window without breaking the other window's ownership

- destroys one window without breaking the other window's ownership
   - Expected: ids.len() equals `2`
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `1`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `1`
   - Expected: launcher_get_process_window_count(0) equals `1`
   - Expected: launcher_get_app_window_count(5) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destroys one window without breaking the other window's ownership")
launcher_init()
val pid: u64 = 8503
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 421))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 422))
val ids = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids.len()).to_equal(2)

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
    src_port: 421
))

expect(shell.compositor.window_count()).to_equal(1)
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)
expect(launcher_get_process_window_count(0)).to_equal(1)
expect(launcher_get_app_window_count(5)).to_equal(1)
```

</details>

#### rejects a client destroying another client's window

- rejects a client destroying another client's window
   - Expected: ids.len() equals `2`
   - Expected: shell.compositor.window_count() equals `2`
   - Expected: shell.compositor.window_owner_port(ids[0]) equals `431`
   - Expected: shell.wm.window_owner_app_id(ids[0]) equals `/sys/apps/browser_demo`
   - Expected: launcher_get_app_window_count(5) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a client destroying another client's window")
launcher_init()
val pid: u64 = 8504
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Owner", pid, 431))
shell.apply_wm_action(_create_window_action("Attacker", pid, 432))
val ids = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids.len()).to_equal(2)

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
    src_port: 432
))

expect(shell.compositor.window_count()).to_equal(2)
expect(shell.compositor.window_owner_port(ids[0])).to_equal(431)
expect(shell.wm.window_owner_app_id(ids[0])).to_equal("/sys/apps/browser_demo")
expect(launcher_get_app_window_count(5)).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/apps/browser_demo_launcher_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser Demo launcher lifecycle.
- Browser Demo launcher lifecycle

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

- Canonical SPipe generation for source `711075ad2c9f79efe93954e78af78fd8d4d28670cff5ba12bc6ecabfaf49e269`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `711075ad2c9f79efe93954e78af78fd8d4d28670cff5ba12bc6ecabfaf49e269`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `711075ad2c9f79efe93954e78af78fd8d4d28670cff5ba12bc6ecabfaf49e269`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/apps/browser_demo_launcher_lifecycle_spec.spl
mirror: doc/06_spec/unit/os/apps/browser_demo_launcher_lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/browser_demo_launcher_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/browser_demo_launcher_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/browser_demo_launcher_lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/apps/browser_demo_launcher_lifecycle_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the built-in browser_demo manifest identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/browser_demo_launcher_lifecycle_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups two remote windows under one launcher-owned app_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/browser_demo_launcher_lifecycle_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps grouping stable after a title change on one window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
