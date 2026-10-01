# Shell Taskbar Pin Specification

> Tests covering SimpleOS taskbar pin authority.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Taskbar Pin Specification

## Scenarios

### SimpleOS taskbar pin authority

#### uses stable ordered app ids and idempotent mutations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses stable ordered app ids and idempotent mutations
   - Expected: _mount_hosted_rootfs_for_test(taskbar_test_root()) is true
   - Expected: shell.pinned_app_count() equals `baseline + 1`
   - Expected: pinned[pinned.len() - 1].display_name equals `Demo`
   - Expected: shell.unpin_app("/sys/apps/demo") is true
   - Expected: shell.unpin_app("/sys/apps/demo") is false
   - Expected: shell.pinned_app_count() equals `baseline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses stable ordered app ids and idempotent mutations")
_vfs_ambient_reset_for_test()
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(taskbar_test_root())).to_equal(true)
var shell = taskbar_test_shell()
val baseline = shell.pinned_app_count()
expect(shell.runtime_taskbar_model().pinned[0].app_id).to_equal(
    "/sys/apps/hello_world"
)
expect(shell.pin_app(
    "/sys/apps/demo", "Demo", "D"
)).to_equal(true)
expect(shell.pin_app(
    "/sys/apps/demo", "Ignored", "X"
)).to_equal(true)
expect(shell.pinned_app_count()).to_equal(baseline + 1)
val pinned = shell.runtime_taskbar_model().pinned
expect(pinned[pinned.len() - 1].app_id).to_equal(
    "/sys/apps/demo"
)
expect(pinned[pinned.len() - 1].display_name).to_equal("Demo")
val window = shell.compositor.create_window(
    "Demo Window", 1, 1, 40, 40
)
shell.compositor.set_window_identity(
    window, 42, "/sys/apps/demo"
)
expect(shell.unpin_app("/sys/apps/demo")).to_equal(true)
expect(shell.unpin_app("/sys/apps/demo")).to_equal(false)
expect(shell.pinned_app_count()).to_equal(baseline)
val running = shell.runtime_taskbar_model().running
expect(running[running.len() - 1].app_id).to_equal(
    "/sys/apps/demo"
)
_clear_vfs_rootfs_for_test()
```

</details>

#### persists pins through the mounted SimpleOS VFS

- persists pins through the mounted SimpleOS VFS
   - Expected: _mount_hosted_rootfs_for_test(taskbar_test_root()) is true
   - Expected: restored.load_pinned_layout() is true
   - Expected: restored.pinned_app_count() equals `baseline + 1`
   - Expected: restored.runtime_taskbar_model().running.len() equals `1`
   - Expected: restored.runtime_taskbar_model().running.len() equals `0`
   - Expected: restored.unpin_app("/sys/apps/demo") is true
   - Expected: unpinned.load_pinned_layout() is true
   - Expected: unpinned.pinned_app_count() equals `baseline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("persists pins through the mounted SimpleOS VFS")
_vfs_ambient_reset_for_test()
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(taskbar_test_root())).to_equal(true)
var first = taskbar_test_shell()
val baseline = first.pinned_app_count()
expect(first.pin_app(
    "/sys/apps/demo", "Demo", "D"
)).to_equal(true)

var restored = taskbar_test_shell()
expect(restored.load_pinned_layout()).to_equal(true)
expect(restored.pinned_app_count()).to_equal(baseline + 1)
expect(restored.pinned_display_name(
    "/sys/apps/demo"
)).to_equal("Demo")
val window = restored.compositor.create_window(
    "Demo Window", 1, 1, 40, 40
)
restored.compositor.set_window_identity(
    window, 42, "/sys/apps/demo"
)
expect(restored.runtime_taskbar_model().running.len()).to_equal(1)
restored.compositor.destroy_window(window)
expect(restored.runtime_taskbar_model().running.len()).to_equal(0)
expect(restored.unpin_app("/sys/apps/demo")).to_equal(true)

var unpinned = taskbar_test_shell()
expect(unpinned.load_pinned_layout()).to_equal(true)
expect(unpinned.pinned_app_count()).to_equal(baseline)
expect(unpinned.pinned_display_name(
    "/sys/apps/demo"
)).to_equal("")
_clear_vfs_rootfs_for_test()
```

</details>

#### rolls pin mutations back when persistence fails

- rolls pin mutations back when persistence fails
   - Expected: shell.pinned_app_count() equals `baseline`
   - Expected: _mount_hosted_rootfs_for_test(taskbar_test_root()) is true
   - Expected: shell.unpin_app("/sys/apps/demo") is false
   - Expected: shell.pinned_app_count() equals `baseline + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rolls pin mutations back when persistence fails")
_vfs_ambient_reset_for_test()
_clear_vfs_rootfs_for_test()
var shell = taskbar_test_shell()
val baseline = shell.pinned_app_count()
expect(shell.pin_app(
    "/sys/apps/demo", "Demo", "D"
)).to_equal(false)
expect(shell.pinned_app_count()).to_equal(baseline)

expect(_mount_hosted_rootfs_for_test(taskbar_test_root())).to_equal(true)
expect(shell.pin_app(
    "/sys/apps/demo", "Demo", "D"
)).to_equal(true)
_clear_vfs_rootfs_for_test()
expect(shell.unpin_app("/sys/apps/demo")).to_equal(false)
expect(shell.pinned_app_count()).to_equal(baseline + 1)
expect(shell.pinned_display_name(
    "/sys/apps/demo"
)).to_equal("Demo")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/shell_taskbar_pin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS taskbar pin authority.
- SimpleOS taskbar pin authority

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f15c9c39b2d618d2449ae62bff479ddc5c0fcec60e7edaa55e3236e0032534c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f15c9c39b2d618d2449ae62bff479ddc5c0fcec60e7edaa55e3236e0032534c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f15c9c39b2d618d2449ae62bff479ddc5c0fcec60e7edaa55e3236e0032534c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/desktop/shell_taskbar_pin_spec.spl
mirror: doc/06_spec/01_unit/os/desktop/shell_taskbar_pin_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/desktop/shell_taskbar_pin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/desktop/shell_taskbar_pin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/desktop/shell_taskbar_pin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/desktop/shell_taskbar_pin_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses stable ordered app ids and idempotent mutations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/shell_taskbar_pin_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists pins through the mounted SimpleOS VFS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/shell_taskbar_pin_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rolls pin mutations back when persistence fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
