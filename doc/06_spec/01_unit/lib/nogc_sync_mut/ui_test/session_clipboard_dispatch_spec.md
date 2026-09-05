# UISession Clipboard Dispatch Spec

> `UISession` owns one `ClipboardService` per session (constructed at runtime in each `UISession.new*`, never as a module-level singleton) and wires `UIEvent.Copy` / `Cut` / `Paste` / `PasteFromHistory` — plus the editor's pre-existing `editor.edit.cut` / `editor.edit.copy` / `editor.edit.paste` / `editor.edit.paste_history_N` button actions — to it through `dispatch()`. This spec proves the end-to-end path real apps (like `src/os/apps/editor/editor.spl`) exercise: focus an input, Copy/Cut/Paste through `session.dispatch`, and paste from history — plus that a default-deny `CapabilityPolicy` blocks clipboard access entirely.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UISession Clipboard Dispatch Spec

`UISession` owns one `ClipboardService` per session (constructed at runtime in each `UISession.new*`, never as a module-level singleton) and wires `UIEvent.Copy` / `Cut` / `Paste` / `PasteFromHistory` — plus the editor's pre-existing `editor.edit.cut` / `editor.edit.copy` / `editor.edit.paste` / `editor.edit.paste_history_N` button actions — to it through `dispatch()`. This spec proves the end-to-end path real apps (like `src/os/apps/editor/editor.spl`) exercise: focus an input, Copy/Cut/Paste through `session.dispatch`, and paste from history — plus that a default-deny `CapabilityPolicy` blocks clipboard access entirely.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`UISession` owns one `ClipboardService` per session (constructed at
runtime in each `UISession.new*`, never as a module-level singleton) and
wires `UIEvent.Copy` / `Cut` / `Paste` / `PasteFromHistory` — plus the
editor's pre-existing `editor.edit.cut` / `editor.edit.copy` /
`editor.edit.paste` / `editor.edit.paste_history_N` button actions — to it
through `dispatch()`. This spec proves the end-to-end path real apps (like
`src/os/apps/editor/editor.spl`) exercise: focus an input, Copy/Cut/Paste
through `session.dispatch`, and paste from history — plus that a
default-deny `CapabilityPolicy` blocks clipboard access entirely.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** N/A

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

A one-input session: type a value in (via `set_prop`), copy it, change the
value, cut it (clearing the field), then paste — the field is restored.
Three sequential copies build history; `UIEvent.PasteFromHistory(1)` writes
the middle entry back into the focused input. The same sequence driven
through `UIEvent.Action("editor.edit.copy")` etc. (what editor.spl's
buttons actually emit) proves the button wiring, not just the raw event
API. A session built with `UISession.new_with_policy` and a default-deny
policy shows Copy/Paste are no-ops when ClipboardRead/Write aren't granted.

## Scenarios

### UISession — Copy/Cut/Paste on the focused widget

#### Copy reads the focused input's value into ClipboardService without changing it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Copy reads the focused input's value into ClipboardService without changing it
- Focus the input, seed a value, then Copy
   - Expected: session.clipboard.history_len() equals `1`
   - Expected: WidgetNode(id: "copy_field").get_prop("value") equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Copy reads the focused input's value into ClipboardService without changing it")
step("Focus the input, seed a value, then Copy")
var session = one_input_session("copy")
WidgetNode(id: "copy_field").set_prop("value", "hello world")
session.dispatch(UIEvent.Copy)

expect(session.clipboard.history_len()).to_equal(1)
expect(WidgetNode(id: "copy_field").get_prop("value")).to_equal("hello world")
```

</details>

#### Cut moves the value into ClipboardService and clears the field

- Cut moves the value into ClipboardService and clears the field
- Focus the input, seed a value, then Cut
   - Expected: current.data equals `cut-me`
   - Expected: WidgetNode(id: "cut_field").get_prop("value") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Cut moves the value into ClipboardService and clears the field")
step("Focus the input, seed a value, then Cut")
var session = one_input_session("cut")
WidgetNode(id: "cut_field").set_prop("value", "cut-me")
session.dispatch(UIEvent.Cut)

val current = session.clipboard.paste()
assert_true(current != nil)
if current != nil:
    expect(current.data).to_equal("cut-me")
expect(WidgetNode(id: "cut_field").get_prop("value")).to_equal("")
```

</details>

#### Paste writes the current clipboard entry into the focused field

- Paste writes the current clipboard entry into the focused field
- Cut from one field, then paste into it again
   - Expected: WidgetNode(id: "paste_field").get_prop("value") equals ``
   - Expected: WidgetNode(id: "paste_field").get_prop("value") equals `round-trip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Paste writes the current clipboard entry into the focused field")
step("Cut from one field, then paste into it again")
var session = one_input_session("paste")
WidgetNode(id: "paste_field").set_prop("value", "round-trip")
session.dispatch(UIEvent.Cut)
expect(WidgetNode(id: "paste_field").get_prop("value")).to_equal("")

session.dispatch(UIEvent.Paste)
expect(WidgetNode(id: "paste_field").get_prop("value")).to_equal("round-trip")
```

</details>

### UISession — clipboard HISTORY via PasteFromHistory

#### three copies build history; PasteFromHistory(1) restores the middle one

- three copies build history; PasteFromHistory(1) restores the middle one
- Copy three distinct values in order
   - Expected: session.clipboard.history_len() equals `3`
- Paste from history index 1 (the middle entry, 'second')
   - Expected: WidgetNode(id: "hist_field").get_prop("value") equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("three copies build history; PasteFromHistory(1) restores the middle one")
step("Copy three distinct values in order")
var session = one_input_session("hist")
WidgetNode(id: "hist_field").set_prop("value", "first")
session.dispatch(UIEvent.Copy)
WidgetNode(id: "hist_field").set_prop("value", "second")
session.dispatch(UIEvent.Copy)
WidgetNode(id: "hist_field").set_prop("value", "third")
session.dispatch(UIEvent.Copy)
expect(session.clipboard.history_len()).to_equal(3)

step("Paste from history index 1 (the middle entry, 'second')")
session.dispatch(UIEvent.PasteFromHistory(index: 1))
expect(WidgetNode(id: "hist_field").get_prop("value")).to_equal("second")
```

</details>

### UISession — editor.edit.* button actions (editor.spl's real wiring)

#### editor.edit.copy / editor.edit.cut / editor.edit.paste route through the same clipboard path

- editor.edit.copy / editor.edit.cut / editor.edit.paste route through the same clipboard path
- Copy via the button action name, not the raw UIEvent.Copy
   - Expected: session.clipboard.history_len() equals `1`
- Cut via the button action name clears the field
   - Expected: WidgetNode(id: "btn_field").get_prop("value") equals ``
- Paste via the button action name restores it
   - Expected: WidgetNode(id: "btn_field").get_prop("value") equals `button-copied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("editor.edit.copy / editor.edit.cut / editor.edit.paste route through the same clipboard path")
step("Copy via the button action name, not the raw UIEvent.Copy")
var session = one_input_session("btn")
WidgetNode(id: "btn_field").set_prop("value", "button-copied")
session.dispatch(UIEvent.Action(name: "editor.edit.copy"))
expect(session.clipboard.history_len()).to_equal(1)

step("Cut via the button action name clears the field")
session.dispatch(UIEvent.Action(name: "editor.edit.cut"))
expect(WidgetNode(id: "btn_field").get_prop("value")).to_equal("")

step("Paste via the button action name restores it")
session.dispatch(UIEvent.Action(name: "editor.edit.paste"))
expect(WidgetNode(id: "btn_field").get_prop("value")).to_equal("button-copied")
```

</details>

#### editor.edit.paste_history_N routes to PasteFromHistory(N) (the Paste History button)

- editor.edit.paste_history_N routes to PasteFromHistory(N) (the Paste History button)
- Build two-entry history, then use the paste_history_1 button action
   - Expected: WidgetNode(id: "btnhist_field").get_prop("value") equals `older`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("editor.edit.paste_history_N routes to PasteFromHistory(N) (the Paste History button)")
step("Build two-entry history, then use the paste_history_1 button action")
var session = one_input_session("btnhist")
WidgetNode(id: "btnhist_field").set_prop("value", "older")
session.dispatch(UIEvent.Action(name: "editor.edit.copy"))
WidgetNode(id: "btnhist_field").set_prop("value", "newer")
session.dispatch(UIEvent.Action(name: "editor.edit.copy"))

session.dispatch(UIEvent.Action(name: "editor.edit.paste_history_1"))
expect(WidgetNode(id: "btnhist_field").get_prop("value")).to_equal("older")
```

</details>

### UISession — capability gating denies clipboard access

#### a default-deny CapabilityPolicy blocks Copy (no ClipboardWrite grant)

- a default-deny CapabilityPolicy blocks Copy (no ClipboardWrite grant)
- Build a session whose policy grants nothing
   - Expected: session.clipboard.history_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a default-deny CapabilityPolicy blocks Copy (no ClipboardWrite grant)")
step("Build a session whose policy grants nothing")
val root = column("deny_root", [text_input("deny_field", "placeholder")])
val tree = build_tree(root)
val policy = CapabilityPolicy.new("deny_window")
var session = UISession.new_with_policy(tree, policy)
session.dispatch(UIEvent.FocusEvent(target_id: "deny_field", kind: "focus"))
WidgetNode(id: "deny_field").set_prop("value", "should-not-copy")

session.dispatch(UIEvent.Copy)
expect(session.clipboard.history_len()).to_equal(0)
```

</details>

#### granting ClipboardWrite/ClipboardRead lets Copy/Paste through the same policy-gated session

- granting ClipboardWrite/ClipboardRead lets Copy/Paste through the same policy-gated session
- Build a session whose policy explicitly grants both capabilities
   - Expected: session.clipboard.history_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("granting ClipboardWrite/ClipboardRead lets Copy/Paste through the same policy-gated session")
step("Build a session whose policy explicitly grants both capabilities")
val root = column("grant_root", [text_input("grant_field", "placeholder")])
val tree = build_tree(root)
var policy = CapabilityPolicy.new("grant_window")
policy = grant(policy, Capability.ClipboardWrite)
policy = grant(policy, Capability.ClipboardRead)
var session = UISession.new_with_policy(tree, policy)
session.dispatch(UIEvent.FocusEvent(target_id: "grant_field", kind: "focus"))
WidgetNode(id: "grant_field").set_prop("value", "granted-value")

session.dispatch(UIEvent.Copy)
expect(session.clipboard.history_len()).to_equal(1)
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


## Related Documentation

- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `690ebe1716004d94f74b3164ce99af2548e9d9e2112ed2892df5293a64ee67a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `690ebe1716004d94f74b3164ce99af2548e9d9e2112ed2892df5293a64ee67a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `690ebe1716004d94f74b3164ce99af2548e9d9e2112ed2892df5293a64ee67a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Copy reads the focused input's value into ClipboardService without changing it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Cut moves the value into ClipboardService and clears the field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/ui_test/session_clipboard_dispatch_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Paste writes the current clipboard entry into the focused field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
