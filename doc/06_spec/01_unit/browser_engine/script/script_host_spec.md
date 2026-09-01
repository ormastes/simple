# ScriptHost Specification

> Tests for `ScriptHost` in `src/lib/gc_async_mut/gpu/browser_engine/script/script_host.spl` (REQ-1 / AC-1). All specs FAIL until that module is implemented.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ScriptHost Specification

Tests for `ScriptHost` in `src/lib/gc_async_mut/gpu/browser_engine/script/script_host.spl` (REQ-1 / AC-1). All specs FAIL until that module is implemented.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M15-SCRIPT-HOST |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/browser_engine/script/script_host_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `ScriptHost` in
`src/lib/gc_async_mut/gpu/browser_engine/script/script_host.spl` (REQ-1 / AC-1).
All specs FAIL until that module is implemented.

## Key Behaviors

- `ScriptHost.new()` creates a host ready to execute scripts.
- After creation: `dom_dirty()` is false, `console_buffer().entries()` is empty.
- `execute(source, dom_root)` does not panic on an empty script string.
- `dom_dirty()` starts false, `clear_dirty()` resets it.
- `inject_dom_event(event)` accepts a `BeDomEvent` without crashing when no
  listener is registered.
- `tick(now_micros)` can be called without an execute having run first.

## Scenarios

### ScriptHost

### security boundary

#### denies legacy Simple source and paths without ambient host execution

- denies legacy Simple source and paths without ambient host execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("denies legacy Simple source and paths without ambient host execution")
val runner = ScriptRunner.new()
expect(run_script(
    runner,
    "use std.process.*\nprocess_run(\"sh\", [\"-c\", \"id\"])"
)).to_equal(
    "simple-script-error: ambient host execution disabled"
)
expect(run_script_file(
    runner, "/etc/passwd"
)).to_equal(
    "simple-script-error: ambient host execution disabled"
)
```

</details>

### AC-1: lifecycle — creation

#### AC-1: new ScriptHost has dom_dirty false

- AC-1: new ScriptHost has dom_dirty false
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: new ScriptHost has dom_dirty false")
val host = _make_host()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: new ScriptHost has empty console buffer

- AC-1: new ScriptHost has empty console buffer
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: new ScriptHost has empty console buffer")
val host = _make_host()
val buf = host.console_buffer()
val count = buf.entries().len()
expect(count).to_equal(0)
```

</details>

### AC-1: execute — basic script intake

#### AC-1: execute with empty string does not crash

- AC-1: execute with empty string does not crash
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: execute with empty string does not crash")
var host = _make_host()
val root = _make_div_root()
val _ = _install_host_document(host, root)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: execute_with_type captures transpiled console output

- AC-1: execute_with_type captures transpiled console output
   - Expected: entries.len() equals `3`
   - Expected: entries[0].level equals `log`
   - Expected: entries[1].level equals `warn`
   - Expected: entries[2].level equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: execute_with_type captures transpiled console output")
var host = _make_host()
val root = _make_div_root()
host.execute_with_type("console.log(\"hello from js\")\nconsole.warn(\"careful\")\nconsole.error(\"bad\")", "text/javascript", root)
val entries = host.console_buffer().entries()
expect(entries.len()).to_equal(3)
expect(entries[0].level).to_equal("log")
expect(entries[0].message).to_contain("hello from js")
expect(entries[1].level).to_equal("warn")
expect(entries[1].message).to_contain("careful")
expect(entries[2].level).to_equal("error")
expect(entries[2].message).to_contain("bad")
```

</details>

### AC-1: dirty flag management

#### AC-1: dom_dirty starts false before any tick

- AC-1: dom_dirty starts false before any tick
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: dom_dirty starts false before any tick")
val host = _make_host()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: clear_dirty leaves dom_dirty false when already false

- AC-1: clear_dirty leaves dom_dirty false when already false
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: clear_dirty leaves dom_dirty false when already false")
var host = _make_host()
host.clear_dirty()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

### AC-1: tick — callable without prior execute

#### AC-1: tick with zero timestamp does not crash

- AC-1: tick with zero timestamp does not crash
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: tick with zero timestamp does not crash")
var host = _make_host()
host.tick(0)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: tick with large timestamp does not crash

- AC-1: tick with large timestamp does not crash
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: tick with large timestamp does not crash")
var host = _make_host()
host.tick(9999999999)
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

### AC-1: inject_dom_event — no registered listeners

#### AC-1: inject_dom_event does not crash when no listeners registered

- AC-1: inject_dom_event does not crash when no listeners registered
   - Expected: dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: inject_dom_event does not crash when no listeners registered")
var host = _make_host()
val index = _install_host_document(host, _make_div_root())
val event = _make_click_event()
host.inject_dom_event_route(
    DomNodeRoute(
        generation: index.generation,
        node_id: host.dom_root().node_id
    ),
    event
).unwrap()
val dirty = host.dom_dirty()
expect(dirty).to_equal(false)
```

</details>

#### AC-1: inject_dom_event executes deterministic set-text listener action

- AC-1: inject_dom_event executes deterministic set-text listener action
   - Expected: host.dom_dirty() is true
   - Expected: host.dom_root().text_content equals `clicked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: inject_dom_event executes deterministic set-text listener action")
var host = _make_host()
var root = _make_div_root()
root.add_event_listener("click", "set-text:clicked")
val index = _install_host_document(host, root)
val event = BeDomEvent.create("click", "", true, true)
host.inject_dom_event_route(
    DomNodeRoute(
        generation: index.generation, node_id: root.node_id
    ),
    event
).unwrap()
expect(host.dom_dirty()).to_equal(true)
expect(host.dom_root().text_content).to_equal("clicked")
```

</details>

#### AC-1: deterministic listener action sets and removes attributes

- AC-1: deterministic listener action sets and removes attributes
   - Expected: root.get_attr("aria-expanded") equals `true`
   - Expected: root.has_attr("aria-expanded") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: deterministic listener action sets and removes attributes")
var root = _make_div_root()
root = script_host_apply_event_action(root, "set-attr:aria-expanded=true")
expect(root.get_attr("aria-expanded")).to_equal("true")
root = script_host_apply_event_action(root, "remove-attr:aria-expanded")
expect(root.has_attr("aria-expanded")).to_equal(false)
```

</details>

#### AC-1: deterministic listener action updates class tokens

- AC-1: deterministic listener action updates class tokens
   - Expected: root.classes.len() equals `1`
   - Expected: root.classes.len() equals `0`
   - Expected: root.classes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: deterministic listener action updates class tokens")
var root = _make_div_root()
root = script_host_apply_event_action(root, "add-class:active")
expect(root.classes).to_contain("active")
root = script_host_apply_event_action(root, "add-class:active")
expect(root.classes.len()).to_equal(1)
root = script_host_apply_event_action(root, "toggle-class:active")
expect(root.classes.len()).to_equal(0)
root = script_host_apply_event_action(root, "toggle-class:active")
expect(root.classes).to_contain("active")
root = script_host_apply_event_action(root, "remove-class:active")
expect(root.classes.len()).to_equal(0)
```

</details>

#### AC-1: targeted actions stop at the first matching DOM identity

- AC-1: targeted actions stop at the first matching DOM identity
   - Expected: updated.children[1].get_attr("data-hit") equals ``
   - Expected: missing.children[1].get_attr("data-hit") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: targeted actions stop at the first matching DOM identity")
var first = BeDomNode.element_with_id(2, "button")
first.set_attr("id", "duplicate")
first.set_attr("data-slot", "first")
var branch = BeDomNode.element_with_id(3, "section")
branch.add_child(first)
var second = BeDomNode.element_with_id(4, "button")
second.set_attr("id", "duplicate")
second.set_attr("data-slot", "second")
var root = _make_div_root()
root.add_child(branch)
root.add_child(second)

val index = dom_identity_index_build(
    root, DomDocumentGeneration.create(1).unwrap()
).unwrap()
val duplicate_route = index.route_for_author_id(
    "duplicate"
).unwrap()
val updated = script_host_apply_action_to_route(
    root, index, duplicate_route,
    "set-attr:data-hit=yes", false
)
expect(updated.children[0].children[0].get_attr(
    "data-hit"
)).to_equal("yes")
expect(updated.children[0].children[0].get_attr(
    "data-slot"
)).to_equal("first")
expect(updated.children[1].get_attr("data-hit")).to_equal("")
expect(updated.children[1].get_attr("data-slot")).to_equal(
    "second"
)
val missing_route = DomNodeRoute(
    generation: index.generation,
    node_id: 9223372036854775807
)
val missing = script_host_apply_action_to_route(
    updated, index, missing_route,
    "set-attr:data-hit=no", false
)
expect(missing.children[0].children[0].get_attr(
    "data-hit"
)).to_equal("yes")
expect(missing.children[1].get_attr("data-hit")).to_equal("")
```

</details>

#### AC-1: inject_dom_event executes deterministic attribute and class actions

- AC-1: inject_dom_event executes deterministic attribute and class actions
   - Expected: host.dom_root().get_attr("data-clicked") equals `yes`
   - Expected: host.dom_dirty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: inject_dom_event executes deterministic attribute and class actions")
var host = _make_host()
var root = _make_div_root()
root.add_event_listener("click", "set-attr:data-clicked=yes")
root.add_event_listener("click", "add-class:clicked")
val index = _install_host_document(host, root)
val event = BeDomEvent.create("click", "", true, true)
host.inject_dom_event_route(
    DomNodeRoute(
        generation: index.generation, node_id: root.node_id
    ),
    event
).unwrap()
expect(host.dom_root().get_attr("data-clicked")).to_equal("yes")
expect(host.dom_root().classes).to_contain("clicked")
expect(host.dom_dirty()).to_equal(true)
```

</details>

#### AC-1: inject_dom_event targets a child and applies its default action

- AC-1: inject_dom_event targets a child and applies its default action
   - Expected: updated.get_attr("data-clicked") equals `yes`
   - Expected: updated.has_attr("checked") is true
   - Expected: host.dom_dirty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: inject_dom_event targets a child and applies its default action")
var host = _make_host()
var checkbox = BeDomNode.element_with_id(2, "input")
checkbox.set_attr("id", "accept")
checkbox.set_attr("type", "checkbox")
checkbox.add_event_listener("click", "set-attr:data-clicked=yes")
var root = _make_div_root()
root.set_attr("id", "root")
root.add_child(checkbox)
val index = _install_host_document(host, root)

val event = BeDomEvent.create("click", "", true, true)
host.inject_dom_event_route(
    index.route_for_author_id("accept").unwrap(), event
).unwrap()

val updated = host.dom_root().children[0]
expect(updated.get_attr("data-clicked")).to_equal("yes")
expect(updated.has_attr("checked")).to_equal(true)
expect(host.dom_dirty()).to_equal(true)
```

</details>

#### AC-1: selecting a radio clears only same-form named peers

- AC-1: selecting a radio clears only same-form named peers


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: selecting a radio clears only same-form named peers")
var first = BeDomNode.element_with_id(11, "input")
first.set_attr("id", "first")
first.set_attr("type", "radio")
first.set_attr("name", "choice")
first.set_attr("checked", "checked")
var second = BeDomNode.element_with_id(12, "input")
second.set_attr("id", "second")
second.set_attr("type", "radio")
second.set_attr("name", "choice")
var other = BeDomNode.element_with_id(13, "input")
other.set_attr("id", "other")
other.set_attr("type", "radio")
other.set_attr("name", "choice")
other.set_attr("checked", "checked")
var form = BeDomNode.element_with_id(10, "form")
form.set_attr("id", "primary")
form.add_child(first)
form.add_child(second)
var other_form = BeDomNode.element_with_id(20, "form")
other_form.set_attr("id", "secondary")
other_form.add_child(other)
var root = _make_div_root()
root.add_child(form)
root.add_child(other_form)
var host = _make_host()
val index = _install_host_document(host, root)

host.inject_dom_event_route(
    index.route_for_author_id("second").unwrap(),
    BeDomEvent.create("click", "", true, true)
).unwrap()

val updated = host.dom_root()
expect(updated.children[0].children[0].has_attr("checked")).to_be(false)
expect(updated.children[0].children[0].has_attr("data-focused")).to_be(false)
expect(updated.children[0].children[1].has_attr("checked")).to_be(true)
expect(updated.children[0].children[1].has_attr("data-focused")).to_be(true)
expect(updated.children[1].children[0].has_attr("checked")).to_be(true)
```

</details>

#### AC-1: submit controls dispatch a cancelable event to their owning form

- AC-1: submit controls dispatch a cancelable event to their owning form
   - Expected: updated.children[1].get_attr("data-submitted") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: submit controls dispatch a cancelable event to their owning form")
var blocked_form = BeDomNode.element_with_id(10, "form")
blocked_form.set_attr("id", "blocked-form")
blocked_form.add_event_listener("submit", "prevent-default")
var blocked_button = BeDomNode.element_with_id(11, "button")
blocked_button.set_attr("id", "blocked-submit")
blocked_form.add_child(blocked_button)
var allowed_form = BeDomNode.element_with_id(20, "form")
allowed_form.set_attr("id", "allowed-form")
var allowed_button = BeDomNode.element_with_id(21, "button")
allowed_button.set_attr("id", "allowed-submit")
allowed_form.add_child(allowed_button)
var root = _make_div_root()
root.add_child(blocked_form)
root.add_child(allowed_form)
var host = _make_host()
val index = _install_host_document(host, root)

host.inject_dom_event_route(
    index.route_for_author_id("blocked-submit").unwrap(),
    BeDomEvent.create("click", "", true, true)
).unwrap()
host.inject_dom_event_route(
    index.route_for_author_id("allowed-submit").unwrap(),
    BeDomEvent.create("click", "", true, true)
).unwrap()

val updated = host.dom_root()
expect(updated.children[0].has_attr("data-submitted")).to_be(false)
expect(updated.children[1].get_attr("data-submitted")).to_equal("true")
```

</details>

#### AC-1: capture actions mutate currentTarget rather than the event target

- AC-1: capture actions mutate currentTarget rather than the event target
   - Expected: host.dom_root().get_attr("data-captured") equals `yes`
   - Expected: host.dom_root().children[0].get_attr("data-captured") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: capture actions mutate currentTarget rather than the event target")
var host = _make_host()
var checkbox = BeDomNode.element_with_id(2, "input")
checkbox.set_attr("id", "accept")
checkbox.set_attr("type", "checkbox")
var root = _make_div_root()
root.set_attr("id", "root")
root.add_event_listener_with_capture("click", "set-attr:data-captured=yes", true)
root.add_child(checkbox)
val index = _install_host_document(host, root)

val event = BeDomEvent.create("click", "", true, true)
host.inject_dom_event_route(
    index.route_for_author_id("accept").unwrap(), event
).unwrap()

expect(host.dom_root().get_attr("data-captured")).to_equal("yes")
expect(host.dom_root().children[0].get_attr("data-captured")).to_equal("")
```

</details>

### AC-1: dom_root — returns current root

#### AC-1: dom_root after execute returns a BeDomNode

- AC-1: dom_root after execute returns a BeDomNode
   - Expected: returned_root.tag equals `div`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-1: dom_root after execute returns a BeDomNode")
var host = _make_host()
val root = _make_div_root()
val _ = _install_host_document(host, root)
val returned_root = host.dom_root()
expect(returned_root.tag).to_equal("div")
```

</details>

### fetch dispatch bridge

#### uses safe fallback when no fetch dispatch is installed

- uses safe fallback when no fetch dispatch is installed
   - Expected: resp.status equals `0`
   - Expected: resp.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("uses safe fallback when no fetch dispatch is installed")
val host = _make_host()
val resp = host.fetch(fetch_create_request("https://example.test/data", "GET"))
expect(resp.status).to_equal(0)
expect(resp.ok).to_equal(false)
```

</details>

#### sends fetch requests through installed dispatch

- sends fetch requests through installed dispatch
   - Expected: resp.status equals `200`
   - Expected: resp.ok is true
   - Expected: resp.headers[0] equals `x-host`
   - Expected: resp.headers[1] equals `yes`
   - Expected: resp.body equals `body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("sends fetch requests through installed dispatch")
var host = _make_host()
host.set_fetch_dispatch(ScriptStaticFetchDispatch.create(200, "x-host: yes", "body"))
val resp = host.fetch(fetch_create_request("https://example.test/data", "GET"))
expect(resp.status).to_equal(200)
expect(resp.ok).to_equal(true)
expect(resp.headers[0]).to_equal("x-host")
expect(resp.headers[1]).to_equal("yes")
expect(resp.body).to_equal("body")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5dd42bfb60e7eb74002bbe85d04849a3527d61f7b92b4a000c048fc3d5fc78bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5dd42bfb60e7eb74002bbe85d04849a3527d61f7b92b4a000c048fc3d5fc78bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5dd42bfb60e7eb74002bbe85d04849a3527d61f7b92b4a000c048fc3d5fc78bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/script/script_host_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/script/script_host_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/script/script_host_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/script/script_host_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/script/script_host_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/script/script_host_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies legacy Simple source and paths without ambient host execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/script/script_host_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: new ScriptHost has dom_dirty false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/script/script_host_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: new ScriptHost has empty console buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
