# browser_demo_launcher_lifecycle_spec

> Verifies the browser demo launcher lifecycle behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_demo_launcher_lifecycle_spec

Verifies the browser demo launcher lifecycle behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/browser_demo_launcher_lifecycle_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser demo launcher lifecycle behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Browser Demo launcher lifecycle

#### exposes the built-in browser_demo manifest identity

- Verify: exposes the built-in browser_demo manifest identity
   - Expected: launcher_get_app_path(5) equals `/sys/apps/browser_demo.smf`
   - Expected: launcher_get_app_identity(5) equals `/sys/apps/browser_demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: exposes the built-in browser_demo manifest identity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
expect(launcher_get_app_path(5)).to_equal("/sys/apps/browser_demo.smf")
expect(launcher_get_app_identity(5)).to_equal("/sys/apps/browser_demo")
```

</details>

#### groups two remote windows under one launcher-owned app_id

- Verify: groups two remote windows under one launcher-owned app_id
   - Expected: shell.compositor.window_count() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.compositor.window_count_for_process(pid) equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.wm.window_count_for_process(pid) equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/browser_demo`
   - Expected: launcher_get_process_window_count(0) equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_get_app_window_count(5) equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_get_app_launch_state(5) equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: groups two remote windows under one launcher-owned app_id")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
val pid: u64 = 8301
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 401))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 402))

expect(shell.compositor.window_count()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(shell.compositor.window_count_for_process(pid)).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(shell.wm.window_count_for_process(pid)).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/browser_demo")
expect(launcher_get_process_window_count(0)).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(launcher_get_app_window_count(5)).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(launcher_get_app_launch_state(5)).to_equal("running")
```

</details>

#### keeps grouping stable after a title change on one window

- Verify: keeps grouping stable after a title change on one window
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: ids_before.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.wm.window_owner_app_id(first_wid) equals `/sys/apps/browser_demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: keeps grouping stable after a title change on one window")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
val pid: u64 = 8402
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 411))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 412))
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)  # oracle: pinned constant asserted by this scenario

val ids_before = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids_before.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
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

expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(shell.wm.window_owner_app_id(first_wid)).to_equal("/sys/apps/browser_demo")
```

</details>

#### destroys one window without breaking the other window's ownership

- Verify: destroys one window without breaking the other window's ownership
   - Expected: ids.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.compositor.window_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_get_process_window_count(0) equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_get_app_window_count(5) equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: destroys one window without breaking the other window's ownership")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
val pid: u64 = 8503
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 421))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 422))
val ids = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario

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

expect(shell.compositor.window_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(launcher_get_process_window_count(0)).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(launcher_get_app_window_count(5)).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects a client destroying another client's window

- Verify: rejects a client destroying another client's window
   - Expected: ids.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.compositor.window_count() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.compositor.window_owner_port(ids[0]) equals `431)  # oracle: pinned constant asserted by this scenario`
   - Expected: shell.wm.window_owner_app_id(ids[0]) equals `/sys/apps/browser_demo`
   - Expected: launcher_get_app_window_count(5) equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: rejects a client destroying another client's window")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
val pid: u64 = 8504
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Owner", pid, 431))
shell.apply_wm_action(_create_window_action("Attacker", pid, 432))
val ids = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario

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

expect(shell.compositor.window_count()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(shell.compositor.window_owner_port(ids[0])).to_equal(431)  # oracle: pinned constant asserted by this scenario
expect(shell.wm.window_owner_app_id(ids[0])).to_equal("/sys/apps/browser_demo")
expect(launcher_get_app_window_count(5)).to_equal(2)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ae09144d759c463afc5864861e6d0bf534860dfb664813b47259300cd381211a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae09144d759c463afc5864861e6d0bf534860dfb664813b47259300cd381211a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae09144d759c463afc5864861e6d0bf534860dfb664813b47259300cd381211a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/apps/browser_demo_launcher_lifecycle_spec.spl
mirror: doc/06_spec/01_unit/os/apps/browser_demo_launcher_lifecycle_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/browser_demo_launcher_lifecycle_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/apps/browser_demo_launcher_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/browser_demo_launcher_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
