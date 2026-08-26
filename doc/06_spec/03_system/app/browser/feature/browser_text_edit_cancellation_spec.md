# Canceled Browser Text Editing

> This specification proves hosted and isolated-worker text controls preserve the same UTF-8 selection when cancelable `beforeinput` blocks Backspace or Delete. Both routes use the canonical BrowserSession DOM event and editing owners.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Canceled Browser Text Editing

This specification proves hosted and isolated-worker text controls preserve the same UTF-8 selection when cancelable `beforeinput` blocks Backspace or Delete. Both routes use the canonical BrowserSession DOM event and editing owners.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/04_architecture/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification proves hosted and isolated-worker text controls preserve the
same UTF-8 selection when cancelable `beforeinput` blocks Backspace or Delete.
Both routes use the canonical BrowserSession DOM event and editing owners.

## Requirements

**Requirements:** doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md

- REQ-WEB-BROWSER-007: cancellation must suppress the default edit without
  corrupting live selection state.
- REQ-WEB-BROWSER-008: keyboard editing, `beforeinput`, `input`, `change`,
  selection movement, and blur must agree across hosted and worker paths.

## Plan

**Plan:** doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md

## Design

**Design:** doc/04_architecture/simple_web_browser_engine_production_hardening.md

## Research

**Research:** doc/01_research/local/simple_web_browser_engine_production_hardening.md

Domain context: `doc/01_research/domain/simple_web_browser_engine_production_hardening.md`

## Behavior and UTF-8 Example

The fixture value is `aéz`. Its selected `é` occupies UTF-8 byte range `1..3`.
Canceled Backspace and Delete must leave the value and selection unchanged.
The observable order is `keydown` then canceled `beforeinput`; neither `input`
nor `change` may follow. Shift+ArrowRight must then extend focus from byte 3 to
byte 4, proving the retained selection was used. Blur finally clears the
selection target and resets both byte offsets to zero.

## Examples

Given the value and byte boundaries:

```text
value:  a é   z
bytes:  0 1-2 3
range:    [1,3)
```

the canceling listener produces this transition:

```text
selection 1..3
  -> keydown Backspace
  -> beforeinput preventDefault()
  -> value remains aéz
  -> selection remains 1..3
```

The next shifted cursor operation proves cancellation retained both ends:

```text
Shift+ArrowRight
  -> anchor remains 1
  -> focus advances from 3 to 4
```

## Host and Worker Parity

The hosted case calls the public input surface used by an in-process Web
window. The worker case sends the unchanged K2 keyboard message through the
isolated renderer session. Both end with identical DOM value, selection,
event title, and blur cleanup.

No test-only editing path is introduced. A difference between these rows means
the hosted adapter or worker IPC adapter bypassed the canonical BrowserSession
default-action owner.

## Failure Discrimination

The assertions distinguish the original bug from nearby failures:

- A changed value means cancellation did not suppress the edit.
- A collapsed `1..1` or `3..3` range means cancellation corrupted selection.
- An `input` entry means a canceled default action still emitted mutation.
- A `change` entry means blur committed a dirty state that never existed.
- A focus byte other than 4 means the next key did not reuse retained state.
- A nonempty target after blur means selection lifetime leaked past focus.

## Scope

This scenario covers cancellation state, UTF-8 byte offsets, event ordering,
host/worker parity, subsequent keyboard selection, and blur cleanup. It does
not add composition-event semantics, clipboard behavior, or a second selection
model; those require separate executable requirements.

## Frozen Steps

The displayed scenario keeps these manual steps in order:

1. Cancel hosted Backspace and Delete over the UTF-8 selection.
2. Extend the retained hosted selection and clear it on blur.
3. Cancel worker K2 Backspace and Delete over the same selection.
4. Extend the retained worker selection and clear it on blur.

The helper checks are executable assertions, not additional event paths or
state owners.

## Scenarios

### Canceled browser text editing

#### should preserve selection and event ordering across hosted and worker paths

- Cancel hosted Backspace and Delete over the UTF-8 selection
   - Expected: hosted_backspace.semantic_target_id equals `q`
- expect canceled text edit
   - Expected: hosted_delete.semantic_target_id equals `q`
- Extend the retained hosted selection and clear it on blur
   - Expected: hosted_shift_right.semantic_target_id equals `q`
- expect shift extended selection
- Cancel worker K2 Backspace and Delete over the same selection
- var worker = HostedBrowserRendererWorkerSession create
- expect canceled text edit
- Extend the retained worker selection and clear it on blur
- expect shift extended selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cancel hosted Backspace and Delete over the UTF-8 selection")
var hosted = HostedWebContentSession.create(
    41, CANCELED_TEXT_EDIT_HTML, 80, 40
)
expect(hosted.browser.set_dom_text_selection("q", 1, 3)).to_be(true)
val hosted_backspace = hosted.dispatch_key_with_shift(
    1, 8, true, false
)
expect(hosted_backspace.semantic_target_id).to_equal("q")
expect_canceled_text_edit(hosted.browser, "beforeinput,")
expect(hosted.browser.set_dom_text_selection("q", 1, 3)).to_be(true)
val hosted_delete = hosted.dispatch_key_with_shift(
    2, 127, true, false
)
expect(hosted_delete.semantic_target_id).to_equal("q")
expect_canceled_text_edit(
    hosted.browser, "beforeinput,beforeinput,"
)

step("Extend the retained hosted selection and clear it on blur")
val hosted_shift_right = hosted.dispatch_key_with_shift(
    3, 39, true, true
)
expect(hosted_shift_right.semantic_target_id).to_equal("q")
expect_shift_extended_selection(hosted.browser)
expect_text_selection_cleanup(
    hosted.browser, "beforeinput,beforeinput,"
)

step("Cancel worker K2 Backspace and Delete over the same selection")
var worker = HostedBrowserRendererWorkerSession.create(80, 40)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: CANCELED_TEXT_EDIT_HTML
)).ok).to_be(true)
expect(worker.browser.set_dom_text_selection("q", 1, 3)).to_be(true)
expect(worker.handle(BrowserRendererMessage(
    kind: "key", generation: 7, request_id: 3,
    payload: "K2\t1\t8\t1\t0"
)).ok).to_be(true)
expect_canceled_text_edit(worker.browser, "beforeinput,")
expect(worker.browser.set_dom_text_selection("q", 1, 3)).to_be(true)
expect(worker.handle(BrowserRendererMessage(
    kind: "key", generation: 7, request_id: 4,
    payload: "K2\t2\t127\t1\t0"
)).ok).to_be(true)
expect_canceled_text_edit(
    worker.browser, "beforeinput,beforeinput,"
)

step("Extend the retained worker selection and clear it on blur")
expect(worker.handle(BrowserRendererMessage(
    kind: "key", generation: 7, request_id: 5,
    payload: "K2\t3\t39\t1\t1"
)).ok).to_be(true)
expect_shift_extended_selection(worker.browser)
expect_text_selection_cleanup(
    worker.browser, "beforeinput,beforeinput,"
)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/04_architecture/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>
