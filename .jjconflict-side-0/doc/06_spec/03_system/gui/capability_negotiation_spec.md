# Capability Negotiation Specification

> Verifies that each UI backend correctly advertises its supported capabilities via `capabilities()`, and that optional trait methods return `Err(NotSupported)` when the capability is absent.

<!-- sdn-diagram:id=capability_negotiation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_negotiation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_negotiation_spec -> std
capability_negotiation_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_negotiation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Negotiation Specification

Verifies that each UI backend correctly advertises its supported capabilities via `capabilities()`, and that optional trait methods return `Err(NotSupported)` when the capability is absent.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-CAP-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/capability_negotiation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that each UI backend correctly advertises its supported
capabilities via `capabilities()`, and that optional trait methods
return `Err(NotSupported)` when the capability is absent.

## Scenarios

### TUI backend capability negotiation

<details>
<summary>Advanced: reports only Color capability</summary>

#### reports only Color capability _(slow)_

1. Ok
   - Expected: has_capability(caps, Capability.Color) is true
   - Expected: has_capability(caps, Capability.Mouse) is false
   - Expected: has_capability(caps, Capability.Images) is false
   - Expected: has_capability(caps, Capability.Touch) is false
   - Expected: has_capability(caps, Capability.NativeDialogs) is false
   - Expected: has_capability(caps, Capability.Notification) is false

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("tui", 0)
match result:
    Ok(backend) :
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Color)).to_equal(true)
        expect(has_capability(caps, Capability.Mouse)).to_equal(false)
        expect(has_capability(caps, Capability.Images)).to_equal(false)
        expect(has_capability(caps, Capability.Touch)).to_equal(false)
        expect(has_capability(caps, Capability.NativeDialogs)).to_equal(false)
        expect(has_capability(caps, Capability.Notification)).to_equal(false)
    Err(e) :
        fail("tui backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: render_image returns Err(NotSupported)</summary>

#### render_image returns Err(NotSupported) _(slow)_

1. Ok

2. Err

3. Ok

4. fail

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("tui", 0)
match result:
    Ok(backend) :
        val node = WidgetNode.new("img1", "image")
        val rect = WidgetRect.new("img1", 0, 0, 100, 100)
        val img_result = backend.render_image(node, rect)
        match img_result:
            Err(ns) :
                expect(ns.backend_name).to_contain("tui")
            Ok(v) :
                fail("tui render_image unexpectedly succeeded")
    Err(e) :
        fail("tui backend creation failed: " + e)
```

</details>


</details>

### Web backend capability negotiation

<details>
<summary>Advanced: reports Mouse, Color, Images, and Touch capabilities</summary>

#### reports Mouse, Color, Images, and Touch capabilities _(slow)_

1. Ok
   - Expected: has_capability(caps, Capability.Mouse) is true
   - Expected: has_capability(caps, Capability.Color) is true
   - Expected: has_capability(caps, Capability.Images) is true
   - Expected: has_capability(caps, Capability.Touch) is true

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("web", 0)
match result:
    Ok(backend) :
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Mouse)).to_equal(true)
        expect(has_capability(caps, Capability.Color)).to_equal(true)
        expect(has_capability(caps, Capability.Images)).to_equal(true)
        expect(has_capability(caps, Capability.Touch)).to_equal(true)
    Err(e) :
        fail("web backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: render_image returns Ok(true)</summary>

#### render_image returns Ok(true) _(slow)_

1. Ok

2. Ok
   - Expected: v is true

3. Err

4. fail

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("web", 0)
match result:
    Ok(backend) :
        val node = WidgetNode.new("web_img", "image")
        val rect = WidgetRect.new("web_img", 0, 0, 200, 150)
        val img_result = backend.render_image(node, rect)
        match img_result:
            Ok(v) :
                expect(v).to_equal(true)
            Err(ns) :
                fail("web render_image returned NotSupported")
    Err(e) :
        fail("web backend creation failed: " + e)
```

</details>


</details>

### None backend capability negotiation

<details>
<summary>Advanced: reports empty capabilities</summary>

#### reports empty capabilities _(slow)_

1. Ok
   - Expected: caps.len() equals `0`

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("none", 0)
match result:
    Ok(backend) :
        val caps = backend.capabilities()
        expect(caps.len()).to_equal(0)
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: show_notification returns Err(NotSupported)</summary>

#### show_notification returns Err(NotSupported) _(slow)_

1. Ok

2. Err
   - Expected: ns.capability equals `Capability.Notification`

3. Ok

4. fail

5. Err

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("none", 0)
match result:
    Ok(backend) :
        val notif_result = backend.show_notification("Test", "Body text")
        match notif_result:
            Err(ns) :
                expect(ns.capability).to_equal(Capability.Notification)
            Ok(v) :
                fail("none show_notification unexpectedly succeeded")
    Err(e) :
        fail("none backend creation failed: " + e)
```

</details>


</details>

### Tauri backend capability negotiation

<details>
<summary>Advanced: reports Mouse, Color, Images, NativeDialogs, and Notification</summary>

#### reports Mouse, Color, Images, NativeDialogs, and Notification _(slow)_

1. Ok
   - Expected: has_capability(caps, Capability.Mouse) is true
   - Expected: has_capability(caps, Capability.Color) is true
   - Expected: has_capability(caps, Capability.Images) is true
   - Expected: has_capability(caps, Capability.NativeDialogs) is true
   - Expected: has_capability(caps, Capability.Notification) is true

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("tauri", 0)
match result:
    Ok(backend) :
        val caps = backend.capabilities()
        expect(has_capability(caps, Capability.Mouse)).to_equal(true)
        expect(has_capability(caps, Capability.Color)).to_equal(true)
        expect(has_capability(caps, Capability.Images)).to_equal(true)
        expect(has_capability(caps, Capability.NativeDialogs)).to_equal(true)
        expect(has_capability(caps, Capability.Notification)).to_equal(true)
    Err(e) :
        fail("tauri backend creation failed: " + e)
```

</details>


</details>

### has_capability helper

<details>
<summary>Advanced: returns false for empty list</summary>

#### returns false for empty list _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps: [Capability] = []
expect(has_capability(caps, Capability.Mouse)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: returns true when capability is present</summary>

#### returns true when capability is present _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = [Capability.Color, Capability.Mouse]
expect(has_capability(caps, Capability.Color)).to_equal(true)
expect(has_capability(caps, Capability.Mouse)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns false when capability is absent</summary>

#### returns false when capability is absent _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = [Capability.Color]
expect(has_capability(caps, Capability.Images)).to_equal(false)
expect(has_capability(caps, Capability.Touch)).to_equal(false)
```

</details>


</details>

### Backend factory error handling

<details>
<summary>Advanced: returns Err for unknown mode</summary>

#### returns Err for unknown mode _(slow)_

1. Err

2. Ok

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("unknown_backend", 0)
match result:
    Err(e) :
        expect(e).to_contain("Unknown backend mode")
    Ok(v) :
        fail("unknown backend mode unexpectedly succeeded")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
