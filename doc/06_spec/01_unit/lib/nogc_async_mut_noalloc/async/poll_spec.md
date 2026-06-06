# Poll Specification

> <details>

<!-- sdn-diagram:id=poll_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=poll_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

poll_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=poll_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Poll Specification

## Scenarios

### Poll

#### defines pending and ready status constants

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val poll = rt_file_read_text("src/lib/nogc_async_mut_noalloc/async/poll.spl")

expect(poll).to_contain("val POLL_PENDING: i32 = 0")
expect(poll).to_contain("val POLL_READY: i32   = 1")
expect(poll).to_contain("class PollResult:")
expect(poll).to_contain("status: i32")
expect(poll).to_contain("value: i64")
```

</details>

#### defines constructors and status predicates

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val poll = rt_file_read_text("src/lib/nogc_async_mut_noalloc/async/poll.spl")
val init = rt_file_read_text("src/lib/nogc_async_mut_noalloc/async/__init__.spl")

expect(poll).to_contain("static fn pending() -> PollResult:")
expect(poll).to_contain("PollResult(status: POLL_PENDING, value: 0)")
expect(poll).to_contain("static fn ready(v: i64) -> PollResult:")
expect(poll).to_contain("PollResult(status: POLL_READY, value: v)")
expect(poll).to_contain("fn is_ready() -> bool:")
expect(poll).to_contain("self.status == POLL_READY")
expect(poll).to_contain("fn is_pending() -> bool:")
expect(poll).to_contain("self.status == POLL_PENDING")
expect(init).to_contain("export POLL_PENDING, POLL_READY, PollResult")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/async/poll_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Poll

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
