# Hosted Web Content Session Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Web Content Session Specification

## Scenarios

### hosted Web content session

#### applies CSS and advances Simple Script and JavaScript animation on the host clock

- Simple Script creates the CSS-targeted red first frame.
- The host monotonic clock keeps requestAnimationFrame pending through 15 ms.
- At 16 ms JavaScript selects the element created by Simple Script, mutates its
  live style, and Engine2D renders a distinct blue frame.

#### commits one HTTPS redirect hop per host tick through browser policy

- The hosted adapter returns the raw 302 response to `BrowserSession` instead
  of consuming the redirect inside Fetch.
- Strict-Transport-Security upgrades the plaintext Location before the next
  request is emitted.
- A second host tick commits the HTTPS document while preserving the previous
  page until that final response arrives.

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

#### routes hosted key edges to DOM focus before window shortcuts

- Focus a hosted text input through the production pointer route.
- Deliver W keydown, committed text, and W keyup to that DOM focus.
- Verify both key listeners run and the input value becomes `w`, preventing
  the bare W edge from becoming a window-close shortcut.
- Focus a checkbox and verify Space keydown reuses the canonical click/default
  path while Space keyup reaches its listener.

#### keeps trusted browser chrome outside hostile page hit testing

- The WM-owned toolbar and address field occupy a reserved region above the
  hostile page frame.
- A toolbar coordinate resolves only to `browser:session#address`, never to
  page DOM hit testing.
- Committed text edits the trusted address draft and Enter submits it through
  BrowserSession; a hostile page control with the same label remains untouched.
- Matching trusted Back and Forward press/release pairs traverse the real
  BrowserSession history without firing the hostile page's `Back` button.
- The canonical Engine2D frame keeps the address field white at its real screen
  coordinate, proving page pixels do not overwrite trusted chrome.

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
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
