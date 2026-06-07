# expect_spec

> Validates the expect module factory functions and option defaults. Cannot test actual retry semantics without a live CDP session, so this spec focuses on the construction and default values.

<!-- sdn-diagram:id=expect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=expect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

expect_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=expect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# expect_spec

Validates the expect module factory functions and option defaults. Cannot test actual retry semantics without a live CDP session, so this spec focuses on the construction and default values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PLAY-003 |
| Category | Stdlib \| Play |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/play/expect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Validates the expect module factory functions and option defaults.
Cannot test actual retry semantics without a live CDP session, so this
spec focuses on the construction and default values.

## Scenarios

### default_expect_options

#### has 5000ms timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_expect_options()
expect(opts.timeout_ms).to_equal(5000)
```

</details>

#### has 100ms poll interval

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_expect_options()
expect(opts.poll_interval_ms).to_equal(100)
```

</details>

#### has empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_expect_options()
expect(opts.message).to_equal("")
```

</details>

### default_wait_for_options

#### state is visible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_wait_for_options()
expect(opts.state).to_equal("visible")
```

</details>

#### timeout is 30000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_wait_for_options()
expect(opts.timeout_ms).to_equal(30000)
```

</details>

### default_screenshot_options

#### image type is png

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_screenshot_options()
expect(opts.image_type).to_equal("png")
```

</details>

#### full_page is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_screenshot_options()
expect(opts.full_page).to_equal(false)
```

</details>

#### quality is 90

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = default_screenshot_options()
expect(opts.quality).to_equal(90)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
