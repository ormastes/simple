# Hello World Launcher Lifecycle Specification

> Tests covering Hello World launcher lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hello World Launcher Lifecycle Specification

## Scenarios

### Hello World launcher lifecycle

#### exposes the built-in hello_world manifest identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes the built-in hello_world manifest identity
   - Expected: launcher_get_app_path(0) equals `/sys/apps/hello_world.smf`
   - Expected: launcher_get_app_identity(0) equals `/sys/apps/hello_world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the built-in hello_world manifest identity")
launcher_init()
expect(launcher_get_app_path(0)).to_equal("/sys/apps/hello_world.smf")
expect(launcher_get_app_identity(0)).to_equal("/sys/apps/hello_world")
```

</details>

#### joins launcher pid, shell WM ownership, and compositor on one window

- joins launcher pid, shell WM ownership, and compositor on one window
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: shell.compositor.window_process_id(wid) equals `pid`
   - Expected: shell.compositor.window_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: shell.wm.window_owner_process_id(wid) equals `pid`
   - Expected: shell.wm.window_owner_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_window_count(0) equals `1`
   - Expected: launcher_get_app_launch_state(0) equals `running`
   - Expected: launcher_get_app_window_count(0) equals `1`
   - Expected: launcher_get_app_last_pid(0) equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins launcher pid, shell WM ownership, and compositor on one window")
launcher_init()
val pid: u64 = 7101
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", pid, 301))

expect(shell.compositor.window_count()).to_equal(1)
val ids = shell.compositor.windows_for_process(pid)
expect(ids.len()).to_equal(1)
val wid = ids[0]
expect(shell.compositor.window_process_id(wid)).to_equal(pid)
expect(shell.compositor.window_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(shell.wm.window_owner_process_id(wid)).to_equal(pid)
expect(shell.wm.window_owner_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_window_count(0)).to_equal(1)
expect(launcher_get_app_launch_state(0)).to_equal("running")
expect(launcher_get_app_window_count(0)).to_equal(1)
expect(launcher_get_app_last_pid(0)).to_equal(pid)
```

</details>

#### handles graceful exit: window is reaped and app slot returns to exited

- handles graceful exit: window is reaped and app slot returns to exited
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: launcher_get_process_state(0) equals `exited`
   - Expected: launcher_get_running_process_count() equals `0`
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(pid) equals `0`
   - Expected: launcher_get_app_launch_state(0) equals `exited`
   - Expected: launcher_get_app_exit_code(0) equals `0`
   - Expected: launcher_get_app_window_count(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles graceful exit: window is reaped and app slot returns to exited")
launcher_init()
val pid: u64 = 7202
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", pid, 302))
expect(shell.compositor.window_count()).to_equal(1)

# Graceful exit: exit code 0 → classified as "exited".
launcher_note_task_probe(pid, false, 0)
expect(launcher_get_process_state(0)).to_equal("exited")
expect(launcher_get_running_process_count()).to_equal(0)

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)
expect(shell.wm.window_count_for_process(pid)).to_equal(0)
expect(launcher_get_app_launch_state(0)).to_equal("exited")
expect(launcher_get_app_exit_code(0)).to_equal(0)
expect(launcher_get_app_window_count(0)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/apps/hello_world_launcher_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hello World launcher lifecycle.
- Hello World launcher lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `b65a672a7537aa79069a834b400a93cda78d0db78ca6354a39f08b9f514bb5a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b65a672a7537aa79069a834b400a93cda78d0db78ca6354a39f08b9f514bb5a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b65a672a7537aa79069a834b400a93cda78d0db78ca6354a39f08b9f514bb5a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/apps/hello_world_launcher_lifecycle_spec.spl
mirror: doc/06_spec/unit/os/apps/hello_world_launcher_lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/hello_world_launcher_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/hello_world_launcher_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/hello_world_launcher_lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/apps/hello_world_launcher_lifecycle_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the built-in hello_world manifest identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/hello_world_launcher_lifecycle_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins launcher pid, shell WM ownership, and compositor on one window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/hello_world_launcher_lifecycle_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles graceful exit: window is reaped and app slot returns to exited' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
