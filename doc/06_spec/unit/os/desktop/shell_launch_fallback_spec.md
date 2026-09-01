# @manual: primary

> Purpose: Prove that DesktopShell process launch materialization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that DesktopShell process launch materialization.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/desktop/shell_launch_fallback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that DesktopShell process launch materialization.
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

### DesktopShell process launch materialization

#### materializes generic process windows using launcher process identity

- Verify: materializes generic process windows using launcher process identity
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: shell.compositor.window_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: shell.wm.window_owner_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_window_count(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: materializes generic process windows using launcher process identity")
launcher_init()
val pid: u64 = 7501
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Hello World", pid)).to_be(true)

expect(shell.compositor.window_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val ids = shell.compositor.windows_for_process(pid)
expect(ids.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val wid = ids[0]
expect(shell.compositor.window_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(shell.wm.window_owner_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_window_count(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### keeps Browser Demo multi-window materialization while using launcher identity

- Verify: keeps Browser Demo multi-window materialization while using launcher identity
   - Expected: shell.compositor.window_count_for_process(pid) equals `2`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: launcher_get_process_window_count(0) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: keeps Browser Demo multi-window materialization while using launcher identity")
launcher_init()
val pid: u64 = 7502
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Browser Demo", pid)).to_be(true)

expect(shell.compositor.window_count_for_process(pid)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(launcher_get_process_window_count(0)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### materializes Simple Browser as a single filesystem-backed window

- Verify: materializes Simple Browser as a single filesystem-backed window
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: wm_ids.len() equals `1`
   - Expected: wm_ids[0] equals `wid`
   - Expected: shell.compositor.window_process_id(wid) equals `pid`
   - Expected: shell.compositor.window_app_id(wid) equals `simple_browser_app_id()`
   - Expected: shell.wm.window_owner_process_id(wid) equals `pid`
   - Expected: shell.wm.window_owner_app_id(wid) equals `simple_browser_app_id()`
   - Expected: shell.compositor.window_title(wid) equals `Simple Browser`
   - Expected: launcher_get_process_window_count(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: materializes Simple Browser as a single filesystem-backed window")
launcher_init()
val pid: u64 = 7504
expect(launcher_record_process(pid, 7, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Simple Browser", pid)).to_be(true)

expect(shell.compositor.window_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val ids = shell.compositor.windows_for_process(pid)
expect(ids.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val wm_ids = shell.wm.window_ids_for_process(pid)
expect(wm_ids.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val wid = ids[0]
expect(wm_ids[0]).to_equal(wid)
expect(shell.compositor.window_process_id(wid)).to_equal(pid)
expect(shell.compositor.window_app_id(wid)).to_equal(simple_browser_app_id())
expect(shell.wm.window_owner_process_id(wid)).to_equal(pid)
expect(shell.wm.window_owner_app_id(wid)).to_equal(simple_browser_app_id())
expect(shell.compositor.window_title(wid)).to_equal("Simple Browser")
expect(launcher_get_process_window_count(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### refuses process materialization when pid is missing

- Verify: refuses process materialization when pid is missing
   - Expected: shell.compositor.window_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: refuses process materialization when pid is missing")
launcher_init()

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Hello World", 0)).to_be(false)
expect(shell.compositor.window_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### refuses process materialization for unknown apps

- Verify: refuses process materialization for unknown apps
   - Expected: shell.compositor.window_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-DESKTOP-001
step("Verify: refuses process materialization for unknown apps")
launcher_init()
val pid: u64 = 7503

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Unknown App", pid)).to_be(false)
expect(shell.compositor.window_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

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
- `REQ-OS-DESKTOP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5c7b4d30b0db0673af977fb3f83041551a52719407fe4cdcbbc5cc49bdec9bc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c7b4d30b0db0673af977fb3f83041551a52719407fe4cdcbbc5cc49bdec9bc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c7b4d30b0db0673af977fb3f83041551a52719407fe4cdcbbc5cc49bdec9bc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/desktop/shell_launch_fallback_spec.spl
mirror: doc/06_spec/unit/os/desktop/shell_launch_fallback_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/os/desktop/shell_launch_fallback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/desktop/shell_launch_fallback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/desktop/shell_launch_fallback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/desktop/shell_launch_fallback_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/os/desktop/shell_launch_fallback_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes generic process windows using launcher process identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/desktop/shell_launch_fallback_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Browser Demo multi-window materialization while using launcher identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/desktop/shell_launch_fallback_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes Simple Browser as a single filesystem-backed window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
