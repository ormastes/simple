# Hosted Web Content Session Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Web Content Session Specification

## Scenarios

### hosted Web content session

#### applies CSS and advances Simple Script and JavaScript animation on the host clock

- Simple Script creates the CSS-targeted red first frame.
- The host monotonic clock keeps requestAnimationFrame pending through 15 ms.
- At 16 ms JavaScript mutates the live DOM and Engine2D renders a distinct
  blue frame.

#### fails closed when no semantic element is hit or focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = HostedWebContentSession.create(
    9, "<input id='name' value='ready'>", 80, 40
)
val miss = session.dispatch_pointer_at(1, 100, 100, false)
expect(miss.reason).to_equal("no-semantic-target")
expect(miss.callback_count).to_equal(0)
val unfocused = session.dispatch_text(2, "Ada")
expect(unfocused.reason).to_equal("no-focused-semantic-target")
expect(unfocused.mutation_revision).to_equal(0)
```

</details>

#### appends committed text only to the actually focused hosted input

- Press and release the input to establish DOM focus.
- Commit `"A"` and then `"da"` as separate host text events.
- The focused input ends with `value="Ada"`; no pointer-position lookup is
  involved in text routing.

#### clicks only after a matching hosted pointer press and release

- A release without a preceding press must not check the checkbox.
- A press followed by a release outside the semantic surface must not click.
- Only a same-target press/release emits the click default action.
- The resulting checked state must change the hosted pixels and survive the
  canonical compositor-to-Engine2D frame.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/hosted/hosted_web_content_session_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hosted Web content session

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
