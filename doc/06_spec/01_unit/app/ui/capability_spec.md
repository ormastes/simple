# Capability Specification

> <details>

<!-- sdn-diagram:id=capability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Specification

## Scenarios

### Capability

#### names each capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(capability_name(Capability.Mouse)).to_equal("mouse input")
expect(capability_name(Capability.Color)).to_equal("color output")
expect(capability_name(Capability.Images)).to_equal("image rendering")
expect(capability_name(Capability.Touch)).to_equal("touch input")
expect(capability_name(Capability.NativeDialogs)).to_equal("native dialogs")
expect(capability_name(Capability.Clipboard)).to_equal("clipboard access")
expect(capability_name(Capability.Notification)).to_equal("notifications")
```

</details>

#### checks capability membership

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = [Capability.Mouse, Capability.Color]
expect(has_capability(caps, Capability.Mouse)).to_equal(true)
expect(has_capability(caps, Capability.Color)).to_equal(true)
expect(has_capability(caps, Capability.Images)).to_equal(false)
expect(has_capability(caps, Capability.Touch)).to_equal(false)
```

</details>

### NotSupported

#### creates with basic constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = NotSupported.new(Capability.Images, "tui")
expect(ns.backend_name).to_equal("tui")
expect(ns.message()).to_contain("tui")
expect(ns.message()).to_contain("image rendering")
```

</details>

#### creates with hint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = NotSupported.with_hint(Capability.Clipboard, "tauri", "not yet wired")
expect(ns.message()).to_contain("not yet wired")
expect(ns.message()).to_contain("clipboard access")
expect(ns.fallback_hint).to_equal("not yet wired")
```

</details>

#### forces callers to handle Result

1. Ok
   - Expected: false is true
2. Err
   - Expected: ns.backend_name equals `tui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: Result<bool, NotSupported> = Err(NotSupported.new(Capability.Images, "tui"))
match result:
    Ok(_) =>
        expect(false).to_equal(true)  # should not reach
    Err(ns) =>
        expect(ns.backend_name).to_equal("tui")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/capability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Capability
- NotSupported

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
