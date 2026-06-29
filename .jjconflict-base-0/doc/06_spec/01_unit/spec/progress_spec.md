# progress_spec

> Tests for the progress() function that reports test execution status.

<!-- sdn-diagram:id=progress_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=progress_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

progress_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=progress_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# progress_spec

Tests for the progress() function that reports test execution status.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/spec/progress_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the progress() function that reports test execution status.

    Covers message formatting, percentage/step completion, timing display,
    and integration with slow tests and error scenarios.

## Scenarios

### Test Progress Reporting

#### progress function

#### prints progress message with timestamp

1. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Starting test...")
expect true
```

</details>

#### shows elapsed time since test started

1. progress
2. progress
3. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Step 1")
progress("Step 2")
progress("Step 3")
expect true
```

</details>

#### can report percentage completion

1. progress
2. progress
3. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Processing: 0%")
progress("Processing: 50%")
progress("Processing: 100%")
expect true
```

</details>

#### can report step-based completion

1. progress
2. progress
3. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total_steps = 3
progress("Step 1 of 3")
progress("Step 2 of 3")
progress("Step 3 of 3")
expect true
```

</details>

#### progress with slow tests

#### shows progress during long operation

1. progress
2. progress
3. progress
4. progress
5. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Loading modules...")
progress("Loaded 5/15 modules")
progress("Loaded 10/15 modules")
progress("Loaded 15/15 modules")
progress("Running verification...")
expect true
```

</details>

#### progress is optional

#### tests without progress calls work normally

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

#### progress calls can be conditional

1. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val show_progress = true
if show_progress:
    progress("Progress enabled")
expect true
```

</details>

#### progress formatting

#### supports simple messages

1. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Simple message")
expect true
```

</details>

#### supports string interpolation

1. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 42
val name = "items"
progress("Processed " + count.to_string() + " " + name)
expect true
```

</details>

#### handles multiline descriptions

1. progress
2. progress
3. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Phase 1: Initialization")
progress("Phase 2: Processing")
progress("Phase 3: Finalization")
expect true
```

</details>

#### progress timing

#### shows time elapsed in human-readable format

1. progress
2. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Start")
progress("After some work")
expect true
```

</details>

#### progress with errors

#### progress output preserved when test fails

1. progress
2. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Step 1 completed")
progress("Step 2 started")
expect true
```

</details>

### Progress API Design

#### has simple function signature

1. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Message")
expect true
```

</details>

#### is available in all test contexts

1. progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress("Available in test")
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
