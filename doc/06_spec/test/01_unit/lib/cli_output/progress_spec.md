# Progress Specification

> 1. progress start

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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Progress Specification

## Scenarios

### cli_output.progress

#### should start progress with total count

1. progress start
   - Expected: _total equals `10`
   - Expected: _is_tty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress_start(10, "Testing...")
expect(_total).to_equal(10)
expect(_is_tty).to_equal(false)
```

</details>

#### should update progress without error

1. progress start
2. progress update
3. progress update
   - Expected: _total equals `5`
   - Expected: _is_tty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress_start(5, "Tests")
progress_update(1, "test/a_spec.spl")
progress_update(2, "test/b_spec.spl")
expect(_total).to_equal(5)
expect(_is_tty).to_equal(false)
```

</details>

#### should finish progress without error

1. progress start
2. progress update
3. progress update
4. progress update
5. progress finish
   - Expected: _total equals `3`
   - Expected: _is_tty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress_start(3, "Running")
progress_update(1, "a.spl")
progress_update(2, "b.spl")
progress_update(3, "c.spl")
progress_finish("3 passed")
expect(_total).to_equal(3)
expect(_is_tty).to_equal(false)
```

</details>

#### should erase progress line without error

1. progress start
2. progress update
3. progress erase
   - Expected: _total equals `2`
   - Expected: _is_tty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
progress_start(2, "Tests")
progress_update(1, "file.spl")
progress_erase()
expect(_total).to_equal(2)
expect(_is_tty).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cli_output/progress_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cli_output.progress

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
