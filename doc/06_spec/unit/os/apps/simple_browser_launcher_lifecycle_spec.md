# Simple Browser Launcher Lifecycle Specification

> Tests covering Simple Browser launcher lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Browser Launcher Lifecycle Specification

## Scenarios

### Simple Browser launcher lifecycle

#### exposes the built-in simple_browser manifest identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes the built-in simple_browser manifest identity
   - Expected: launcher_get_app_path(7) equals `/sys/apps/simple_browser.smf`
   - Expected: launcher_get_app_identity(7) equals `/sys/apps/simple_browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the built-in simple_browser manifest identity")
launcher_init()
expect(launcher_get_app_path(7)).to_equal("/sys/apps/simple_browser.smf")
expect(launcher_get_app_identity(7)).to_equal("/sys/apps/simple_browser")
```

</details>

#### joins launcher pid, shell WM ownership, and compositor on one browser window

- joins launcher pid, shell WM ownership, and compositor on one browser window
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: shell.compositor.window_process_id(wid) equals `pid`
   - Expected: shell.compositor.window_app_id(wid) equals `/sys/apps/simple_browser`
   - Expected: shell.wm.window_owner_process_id(wid) equals `pid`
   - Expected: shell.wm.window_owner_app_id(wid) equals `/sys/apps/simple_browser`
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/simple_browser`
   - Expected: launcher_get_process_window_count(0) equals `1`
   - Expected: launcher_get_app_launch_state(7) equals `running`
   - Expected: launcher_get_app_window_count(7) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins launcher pid, shell WM ownership, and compositor on one browser window")
launcher_init()
val pid: u64 = 9105
expect(launcher_record_process(pid, 7, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Simple Browser", pid, 501))

expect(shell.compositor.window_count()).to_equal(1)
val ids = shell.compositor.windows_for_process(pid)
expect(ids.len()).to_equal(1)
val wid = ids[0]
expect(shell.compositor.window_process_id(wid)).to_equal(pid)
expect(shell.compositor.window_app_id(wid)).to_equal("/sys/apps/simple_browser")
expect(shell.wm.window_owner_process_id(wid)).to_equal(pid)
expect(shell.wm.window_owner_app_id(wid)).to_equal("/sys/apps/simple_browser")
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/simple_browser")
expect(launcher_get_process_window_count(0)).to_equal(1)
expect(launcher_get_app_launch_state(7)).to_equal("running")
expect(launcher_get_app_window_count(7)).to_equal(1)
```

</details>

#### emits deterministic startup and render markers for about:network

- emits deterministic startup and render markers for about:network


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits deterministic startup and render markers for about:network")
val pid: u64 = 9106
val wid: u64 = 77
expect(simple_browser_ready_marker(pid)).to_contain("app_id=/sys/apps/simple_browser")
expect(simple_browser_ready_marker(pid)).to_contain("page={simple_browser_start_page()}")
expect(simple_browser_window_marker(pid, wid)).to_contain("wid=77")
expect(simple_browser_render_marker(pid, wid)).to_contain("page={simple_browser_start_page()}")
expect(simple_browser_render_marker(pid, wid)).to_contain("renderer=simple_web")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/apps/simple_browser_launcher_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Browser launcher lifecycle.
- Simple Browser launcher lifecycle

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

- Canonical SPipe generation for source `e5c6e4087637356f1b598540b590d0644ffc657ca02ad599718b9565df40e479`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5c6e4087637356f1b598540b590d0644ffc657ca02ad599718b9565df40e479`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5c6e4087637356f1b598540b590d0644ffc657ca02ad599718b9565df40e479`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/apps/simple_browser_launcher_lifecycle_spec.spl
mirror: doc/06_spec/unit/os/apps/simple_browser_launcher_lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/simple_browser_launcher_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/simple_browser_launcher_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/simple_browser_launcher_lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/apps/simple_browser_launcher_lifecycle_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the built-in simple_browser manifest identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/simple_browser_launcher_lifecycle_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins launcher pid, shell WM ownership, and compositor on one browser window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/simple_browser_launcher_lifecycle_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits deterministic startup and render markers for about:network' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
