# types_spec

> Validates foundation types, constants, and factory functions for std.play.

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# types_spec

Validates foundation types, constants, and factory functions for std.play.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PLAY-001 |
| Category | Stdlib \| Play |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/play/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Validates foundation types, constants, and factory functions for std.play.

## Scenarios

### Play backend constants

#### defines BACKEND_CDP

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BACKEND_CDP).to_equal("cdp")
```

</details>

#### defines BACKEND_SDL2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BACKEND_SDL2).to_equal("sdl2")
```

</details>

#### defines BACKEND_WM

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BACKEND_WM).to_equal("wm")
```

</details>

#### defines BACKEND_ORCHESTRATOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BACKEND_ORCHESTRATOR).to_equal("orchestrator")
```

</details>

### Play state constants

#### defines STATE_READY

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(STATE_READY).to_equal("ready")
```

</details>

#### defines STATE_CLOSED

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(STATE_CLOSED).to_equal("closed")
```

</details>

#### defines STATE_FAILED

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(STATE_FAILED).to_equal("failed")
```

</details>

### Play timeout defaults

#### expect timeout is 5000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_EXPECT_TIMEOUT_MS).to_equal(5000)
```

</details>

#### action timeout is 30000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_ACTION_TIMEOUT_MS).to_equal(30000)
```

</details>

#### poll interval is 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_POLL_INTERVAL_MS).to_equal(100)
```

</details>

### default_launch_options

#### returns empty executable_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_launch_options()
expect(opts.executable_path).to_equal("")
```

</details>

#### returns empty args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_launch_options()
expect(opts.args.length()).to_equal(0)
```

</details>

#### has xvfb enabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_launch_options()
expect(opts.xvfb).to_equal(true)
```

</details>

#### has headless false by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_launch_options()
expect(opts.headless).to_equal(false)
```

</details>

#### has 30s launch timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_launch_options()
expect(opts.timeout_ms).to_equal(30000)
```

</details>

### default_click_options

#### defaults to left button

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_click_options()
expect(opts.button).to_equal("left")
```

</details>

#### defaults to 1 click

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_click_options()
expect(opts.click_count).to_equal(1)
```

</details>

#### defaults to no force

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_click_options()
expect(opts.force).to_equal(false)
```

</details>

### empty_play_session

#### has empty id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = empty_play_session()
expect(s.id).to_equal("")
```

</details>

#### has closed state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = empty_play_session()
expect(s.state).to_equal("closed")
```

</details>

#### has pid -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = empty_play_session()
expect(s.pid).to_equal(-1)
```

</details>

#### has no windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = empty_play_session()
expect(s.windows.length()).to_equal(0)
```

</details>

### play_error

#### sets code and message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = play_error("TEST_ERR", "test message")
expect(e.code).to_equal("TEST_ERR")
expect(e.message).to_equal("test message")
expect(e.detail).to_equal("")
```

</details>

### play_error_with_detail

#### sets code message and detail

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = play_error_with_detail("CODE", "msg", "extra")
expect(e.code).to_equal("CODE")
expect(e.message).to_equal("msg")
expect(e.detail).to_equal("extra")
```

</details>

### locator_css

#### creates css locator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = locator_css("#button")
expect(loc.selector).to_equal("#button")
expect(loc.strategy).to_equal("css")
expect(loc.nth).to_equal(-1)
```

</details>

### locator_role

#### creates role locator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = locator_role("button", "Submit")
expect(loc.selector).to_equal("button")
expect(loc.strategy).to_equal("role")
expect(loc.has_text).to_equal("Submit")
```

</details>

### locator_test_id

#### creates test-id locator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = locator_test_id("my-btn")
expect(loc.selector).to_equal("my-btn")
expect(loc.strategy).to_equal("test-id")
```

</details>

### locator_text

#### creates text locator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = locator_text("Click me")
expect(loc.selector).to_equal("Click me")
expect(loc.strategy).to_equal("text")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
