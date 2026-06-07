# xvfb_spec

> Validates the xvfb module's platform detection and command wrapping functions. These are pure functions that can run on any platform.

<!-- sdn-diagram:id=xvfb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=xvfb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

xvfb_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=xvfb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# xvfb_spec

Validates the xvfb module's platform detection and command wrapping functions. These are pure functions that can run on any platform.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PLAY-004 |
| Category | Stdlib \| Play |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/play/xvfb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Validates the xvfb module's platform detection and command wrapping
functions. These are pure functions that can run on any platform.

## Scenarios

### Play xvfb platform detection

#### reports at most one platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
if is_linux(): count = count + 1
if is_macos(): count = count + 1
if is_windows(): count = count + 1
expect(count).to_be_less_than(2)
```

</details>

#### reports at least one platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detected = is_linux() or is_macos() or is_windows()
expect(detected).to_equal(true)
```

</details>

### Play xvfb wrap_cmd

#### returns the same command on macOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    val (cmd, args) = wrap_cmd("npm", ["test"])
    expect(cmd).to_equal("npm")
    expect(args[0]).to_equal("test")
```

</details>

#### returns the same command on Windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_windows():
    val (cmd, args) = wrap_cmd("npm", ["test"])
    expect(cmd).to_equal("npm")
```

</details>

### Play xvfb maybe_wrap_cmd

#### does not wrap when force is false on macOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    val (cmd, args) = maybe_wrap_cmd("echo", ["hi"], false)
    expect(cmd).to_equal("echo")
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
