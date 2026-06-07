# Tauri Backend Specification

> 1. Ok

<!-- sdn-diagram:id=tauri_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_backend_spec -> app
tauri_backend_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Backend Specification

## Scenarios

### TauriBackend

#### creates successfully

1. Ok
   - Expected: backend.backend_name() equals `tauri`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TauriBackend.new(3000)
match result:
    Ok(backend) =>
        expect(backend.backend_name()).to_equal("tauri")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### reports correct capabilities

1. Ok
   - Expected: has_capability(caps, Capability.Mouse) is true
   - Expected: has_capability(caps, Capability.Color) is true
   - Expected: has_capability(caps, Capability.Images) is true
   - Expected: has_capability(caps, Capability.NativeDialogs) is true
   - Expected: has_capability(caps, Capability.Notification) is true
   - Expected: has_capability(caps, Capability.Touch) is false
   - Expected: backend.supports_touch() is false
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TauriBackend.new(3000)
match result:
    Ok(backend) =>
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Mouse)).to_equal(true)
        expect(has_capability(caps, Capability.Color)).to_equal(true)
        expect(has_capability(caps, Capability.Images)).to_equal(true)
        expect(has_capability(caps, Capability.NativeDialogs)).to_equal(true)
        expect(has_capability(caps, Capability.Notification)).to_equal(true)
        expect(has_capability(caps, Capability.Touch)).to_equal(false)
        expect(backend.supports_touch()).to_equal(false)
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

#### models Android Tauri WebView as touch capable

1. Ok
   - Expected: has_capability(caps, Capability.Touch) is true
   - Expected: backend.supports_touch() is true
   - Expected: backend.supports_mouse() is true
   - Expected: backend.backend_name() equals `tauri`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TauriBackend.new_android(3000)
match result:
    Ok(backend) =>
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Touch)).to_equal(true)
        expect(backend.supports_touch()).to_equal(true)
        expect(backend.supports_mouse()).to_equal(true)
        expect(backend.backend_name()).to_equal("tauri")
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

#### models iOS Tauri WebView as touch capable

1. Ok
   - Expected: has_capability(caps, Capability.Touch) is true
   - Expected: backend.supports_touch() is true
   - Expected: backend.supports_images() is true
   - Expected: backend.backend_name() equals `tauri`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TauriBackend.new_ios(3000)
match result:
    Ok(backend) =>
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Touch)).to_equal(true)
        expect(backend.supports_touch()).to_equal(true)
        expect(backend.supports_images()).to_equal(true)
        expect(backend.backend_name()).to_equal("tauri")
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

#### has correct viewport

1. Ok
   - Expected: backend.viewport_width() equals `1280`
   - Expected: backend.viewport_height() equals `720`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TauriBackend.new(3000)
match result:
    Ok(backend) =>
        expect(backend.viewport_width()).to_equal(1280)
        expect(backend.viewport_height()).to_equal(720)
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

#### initializes and shuts down

1. Ok
2. Ok
   - Expected: ok is true
3. Err
   - Expected: false is true
4. backend shutdown
5. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = TauriBackend.new(3000)
match result:
    Ok(backend) =>
        val init_result = backend.init()
        match init_result:
            Ok(ok) =>
                expect(ok).to_equal(true)
            Err(_) =>
                expect(false).to_equal(true)
        backend.shutdown()
    Err(_) =>
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/tauri_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TauriBackend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
