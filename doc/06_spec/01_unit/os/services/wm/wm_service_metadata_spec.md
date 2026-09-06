# Wm Service Metadata Specification

> 1. wm register window owner with identity

<!-- sdn-diagram:id=wm_service_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_service_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_service_metadata_spec -> std
wm_service_metadata_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_service_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Service Metadata Specification

## Scenarios

### WmService ownership metadata

#### stores explicit process and app identity

1. wm register window owner with identity
   - Expected: wm.window_owner_process_id(7) equals `1234`
   - Expected: wm.window_owner_app_id(7) equals `app.browser`
   - Expected: wm.window_count_for_process(1234) equals `1`
   - Expected: wm.window_ids_for_process(1234).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
wm.register_window_owner_with_identity(7, 44, 1234, "app.browser")
expect(wm.window_owner_process_id(7)).to_equal(1234)
expect(wm.window_owner_app_id(7)).to_equal("app.browser")
expect(wm.window_count_for_process(1234)).to_equal(1)
expect(wm.window_ids_for_process(1234).len()).to_equal(1)
```

</details>

#### defaults process identity to the owning port

1. wm register window owner
   - Expected: wm.window_owner_process_id(9) equals `55`
   - Expected: wm.window_ids_for_owner_port(55).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
wm.register_window_owner(9, 55)
expect(wm.window_owner_process_id(9)).to_equal(55)
expect(wm.window_ids_for_owner_port(55).len()).to_equal(1)
```

</details>

#### parses create-window identity extension when provided

1. push u32
2. payload push
3. push i32
4. push i32
5. push i32
6. push i32
7. push u64
8. push u32
9. payload push
   - Expected: action.process_id equals `1234`
   - Expected: action.app_id equals `/sys/browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = WmService.new()
var payload: [u8] = []
push_u32(payload, 7)
for ch in "Browser":
    payload.push(ch.to_u8())
push_i32(payload, 10)
push_i32(payload, 20)
push_i32(payload, 640)
push_i32(payload, 480)
push_u64(payload, 1234)
push_u32(payload, 12)
for ch in "/sys/browser":
    payload.push(ch.to_u8())
val action = wm.parse_create_window(77, unsafe_addr_of(payload), payload.len().to_u32())
expect(action.process_id).to_equal(1234)
expect(action.app_id).to_equal("/sys/browser")
```

</details>

#### falls back to launcher-owned app identity when app_id is omitted

1. launcher init
2. launcher register
3. push u32
4. payload push
5. push i32
6. push i32
7. push i32
8. push i32
9. push u64
   - Expected: action.process_id equals `4321`
   - Expected: action.app_id equals `/sys/apps/browser_demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
launcher_register("Browser Demo", "/sys/apps/browser_demo", "B", 0x42, 0)
val recorded = launcher_record_process(4321, 0, "running", 0, 0, true)
expect(recorded).to_be(true)

val wm = WmService.new()
var payload: [u8] = []
push_u32(payload, 7)
for ch in "Browser":
    payload.push(ch.to_u8())
push_i32(payload, 10)
push_i32(payload, 20)
push_i32(payload, 640)
push_i32(payload, 480)
push_u64(payload, 4321)

val action = wm.parse_create_window(77, unsafe_addr_of(payload), payload.len().to_u32())
expect(action.process_id).to_equal(4321)
expect(action.app_id).to_equal("/sys/apps/browser_demo")
```

</details>

#### reuses launcher and WM ownership contract for RISC-V SMF GUI apps

1. launcher init
2. launcher register
3. wm register window owner with identity
4. launcher note window opened
   - Expected: launcher_process_is_process_backed(pid) is true
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/browser_demo.smf`
   - Expected: launcher_get_process_window_count(0) equals `1`
   - Expected: wm.window_owner_process_id(1) equals `pid`
   - Expected: wm.window_owner_app_id(1) equals `/sys/apps/browser_demo.smf`
   - Expected: desktop_app_ownership_valid(pid, "/sys/apps/browser_demo.smf", 1, 1, pid, "/sys/apps/browser_demo.smf") is true
   - Expected: desktop_app_ownership_marker(pid, "/sys/apps/browser_demo.smf", 1, 1) equals `[desktop-e2e] process-backed:ok app=/sys/apps/browser_demo.smf pid=1002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
launcher_register("Browser Demo", "/sys/apps/browser_demo.smf", "B", 0x42, 1)
val pid: u64 = 1002
val recorded = launcher_record_process(pid, 3, "running", 0, 0, true)
expect(recorded).to_be(true)

val wm = WmService.new()
wm.register_window_owner_with_identity(1, 0, pid, "/sys/apps/browser_demo.smf")
launcher_note_window_opened(pid)

expect(launcher_process_is_process_backed(pid)).to_equal(true)
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/browser_demo.smf")
expect(launcher_get_process_window_count(0)).to_equal(1)
expect(wm.window_owner_process_id(1)).to_equal(pid)
expect(wm.window_owner_app_id(1)).to_equal("/sys/apps/browser_demo.smf")

expect(desktop_app_ownership_valid(pid, "/sys/apps/browser_demo.smf", 1, 1, pid, "/sys/apps/browser_demo.smf")).to_equal(true)
expect(desktop_app_ownership_marker(pid, "/sys/apps/browser_demo.smf", 1, 1)).to_equal("[desktop-e2e] process-backed:ok app=/sys/apps/browser_demo.smf pid=1002")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/wm/wm_service_metadata_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WmService ownership metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
