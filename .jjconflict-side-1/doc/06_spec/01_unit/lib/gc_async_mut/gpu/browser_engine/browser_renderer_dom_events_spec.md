# Browser Renderer Dom Events Specification

> Tests covering Browser renderer DOM event basics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Dom Events Specification

## Scenarios

### Browser renderer DOM event basics

#### registers target event listeners with normalized event names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers target event listeners with normalized event names
   - Expected: be_dom_get_event_listener_count(button, "click") equals `2`
   - Expected: be_dom_get_event_listener_count(button, "onclick") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("registers target event listeners with normalized event names")
var button = BeDomNode.element("button")
button.add_event_listener("click", "listener-a")
button.add_event_listener("onclick", "listener-b")

expect(be_dom_get_event_listener_count(button, "click")).to_equal(2)
expect(be_dom_get_event_listener_count(button, "onclick")).to_equal(2)
```

</details>

#### reuses removed listener tombstones without growing the registry

- reuses removed listener tombstones without growing the registry
   - Expected: button.event_listener_types.len() equals `1`
   - Expected: button.event_listener_actions.len() equals `1`
   - Expected: button.event_listener_capture.len() equals `1`
   - Expected: be_dom_get_event_listener_count(button, "click") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reuses removed listener tombstones without growing the registry")
var button = BeDomNode.element("button")
var churn = 0
while churn < 300:
    button.add_event_listener("click", "callable")
    button.remove_event_listener("click", "callable")
    churn = churn + 1
button.add_event_listener("click", "callable")

expect(button.event_listener_types.len()).to_equal(1)
expect(button.event_listener_actions.len()).to_equal(1)
expect(button.event_listener_capture.len()).to_equal(1)
expect(be_dom_get_event_listener_count(button, "click")).to_equal(1)
```

</details>

#### executes listener control through the canonical dispatch cursor

- executes listener control through the canonical dispatch cursor
   - Expected: dispatch.actions.len() equals `6`
   - Expected: dispatch.actions[0] equals `window-capture`
   - Expected: dispatch.actions[1] equals `document-capture`
   - Expected: dispatch.actions[2] equals `target-capture`
   - Expected: dispatch.actions[3] equals `inline`
   - Expected: dispatch.actions[4] equals `callable-cancel`
   - Expected: dispatch.actions[5] equals `callable-halt`
   - Expected: dispatch.event.default_prevented is true
   - Expected: dispatch.event.immediate_propagation_stopped is true
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: dispatch.default_action_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes listener control through the canonical dispatch cursor")
var window = BeDomNode.element("window")
window.set_attr("id", "window")
window.add_event_listener_with_capture(
    "click", "window-capture", true
)
window.add_event_listener("click", "window-bubble")
var document = BeDomNode.element("document")
document.set_attr("id", "document")
document.add_event_listener_with_capture(
    "click", "document-capture", true
)
document.add_event_listener("click", "document-bubble")
var button = BeDomNode.element("button")
button.set_attr("id", "save")
button.set_attr("onclick", "inline")
button.add_event_listener_with_capture(
    "click", "target-capture", true
)
button.add_event_listener("click", "callable-cancel")
button.add_event_listener("click", "callable-halt")
button.add_event_listener("click", "must-not-run")
document.add_child(button)
window.add_child(document)

val index = _dom_event_index(window)
val route = index.route_for_author_id("save").unwrap()
val dispatch = be_dom_dispatch_event_to_route(
    window, index, route, "click", true, true, true,
    _callable_listener_executor
)

expect(dispatch.actions.len()).to_equal(6)
expect(dispatch.actions[0]).to_equal("window-capture")
expect(dispatch.actions[1]).to_equal("document-capture")
expect(dispatch.actions[2]).to_equal("target-capture")
expect(dispatch.actions[3]).to_equal("inline")
expect(dispatch.actions[4]).to_equal("callable-cancel")
expect(dispatch.actions[5]).to_equal("callable-halt")
expect(dispatch.event.default_prevented).to_equal(true)
expect(dispatch.event.immediate_propagation_stopped).to_equal(true)
expect(dispatch.default_action).to_equal("button-activate")
expect(dispatch.default_action_allowed).to_equal(false)
```

</details>

#### dispatches inline handlers before registered target listeners

- dispatches inline handlers before registered target listeners
   - Expected: actions.len() equals `3`
   - Expected: actions[0] equals `inline-click`
   - Expected: actions[1] equals `listener-a`
   - Expected: actions[2] equals `listener-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatches inline handlers before registered target listeners")
var button = BeDomNode.element("button")
button.set_attr("onclick", "inline-click")
button.add_event_listener("click", "listener-a")
button.add_event_listener("click", "listener-b")

val actions = be_dom_dispatch_event_actions(button, "click")
expect(actions.len()).to_equal(3)
expect(actions[0]).to_equal("inline-click")
expect(actions[1]).to_equal("listener-a")
expect(actions[2]).to_equal("listener-b")
```

</details>

#### keeps unrelated event types isolated

- keeps unrelated event types isolated
   - Expected: input_actions.len() equals `1`
   - Expected: input_actions[0] equals `input-listener`
   - Expected: change_actions.len() equals `1`
   - Expected: change_actions[0] equals `change-listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps unrelated event types isolated")
var input = BeDomNode.element("input")
input.add_event_listener("input", "input-listener")
input.add_event_listener("change", "change-listener")

val input_actions = be_dom_dispatch_event_actions(input, "input")
val change_actions = be_dom_dispatch_event_actions(input, "change")

expect(input_actions.len()).to_equal(1)
expect(input_actions[0]).to_equal("input-listener")
expect(change_actions.len()).to_equal(1)
expect(change_actions[0]).to_equal("change-listener")
```

</details>

#### creates cancelable event payloads without routing authority

- creates cancelable event payloads without routing authority
   - Expected: event.event_type equals `click`
   - Expected: event.target_tag equals `button`
   - Expected: event.current_target_tag equals `button`
   - Expected: event.bubbles is true
   - Expected: event.cancelable is true
   - Expected: event.default_prevented is false
   - Expected: event.default_prevented is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates cancelable event payloads without routing authority")
var button = BeDomNode.element("button")
button.set_attr("id", "save")

var event = BeDomEvent.create("onclick", "", true, true)
event.target_tag = button.tag_name
event.current_target_tag = button.tag_name
expect(event.event_type).to_equal("click")
expect(event.target_tag).to_equal("button")
expect(event.current_target_tag).to_equal("button")
expect(event.bubbles).to_equal(true)
expect(event.cancelable).to_equal(true)
expect(event.default_prevented).to_equal(false)

event.prevent_default()
expect(event.default_prevented).to_equal(true)
```

</details>

#### creates pointer events with basic mouse payload fields

- creates pointer events with basic mouse payload fields
   - Expected: event.event_type equals `mousedown`
   - Expected: event.target_tag equals `button`
   - Expected: event.client_x equals `12`
   - Expected: event.client_y equals `34`
   - Expected: event.screen_x equals `12`
   - Expected: event.screen_y equals `34`
   - Expected: event.button equals `0`
   - Expected: event.buttons equals `1`
   - Expected: event.pointer_id equals `1`
   - Expected: event.pointer_type equals `mouse`
   - Expected: event.is_primary is true
   - Expected: event.alt_key is false
   - Expected: event.ctrl_key is false
   - Expected: event.meta_key is false
   - Expected: event.shift_key is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates pointer events with basic mouse payload fields")
var button = BeDomNode.element("button")
button.set_attr("id", "save")

var event = BeDomEvent.create("mousedown", "", true, true)
event.target_tag = button.tag_name
event.client_x = 12
event.client_y = 34
event.screen_x = 12
event.screen_y = 34
event.button = 0
event.buttons = 1
event.pointer_id = 1
event.pointer_type = "mouse"
event.is_primary = true

expect(event.event_type).to_equal("mousedown")
expect(event.target_tag).to_equal("button")
expect(event.client_x).to_equal(12)
expect(event.client_y).to_equal(34)
expect(event.screen_x).to_equal(12)
expect(event.screen_y).to_equal(34)
expect(event.button).to_equal(0)
expect(event.buttons).to_equal(1)
expect(event.pointer_id).to_equal(1)
expect(event.pointer_type).to_equal("mouse")
expect(event.is_primary).to_equal(true)
expect(event.alt_key).to_equal(false)
expect(event.ctrl_key).to_equal(false)
expect(event.meta_key).to_equal(false)
expect(event.shift_key).to_equal(false)
```

</details>

#### creates pointer events with modifier key state

- creates pointer events with modifier key state
   - Expected: event.event_type equals `click`
   - Expected: event.target_tag equals `button`
   - Expected: event.alt_key is true
   - Expected: event.ctrl_key is false
   - Expected: event.meta_key is true
   - Expected: event.shift_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates pointer events with modifier key state")
var button = BeDomNode.element("button")
button.set_attr("id", "save")

var event = BeDomEvent.create("click", "", true, true)
event.target_tag = button.tag_name
event.client_x = 12
event.client_y = 34
event.pointer_id = 1
event.alt_key = true
event.meta_key = true
event.shift_key = true

expect(event.event_type).to_equal("click")
expect(event.target_tag).to_equal("button")
expect(event.alt_key).to_equal(true)
expect(event.ctrl_key).to_equal(false)
expect(event.meta_key).to_equal(true)
expect(event.shift_key).to_equal(true)
```

</details>

#### leaves non-cancelable events unprevented

- leaves non-cancelable events unprevented
   - Expected: event.default_prevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves non-cancelable events unprevented")
var link = BeDomNode.element("a")
var event = BeDomEvent.create("click", "", true, false)

event.prevent_default()

expect(event.default_prevented).to_equal(false)
```

</details>

#### dispatches actions with event object state

- dispatches actions with event object state
   - Expected: dispatch.event.event_type equals `click`
   - Expected: _dom_event_author_id(index, dispatch.target_route) equals `save`
   - Expected: dispatch.current_targets[0] equals `route`
   - Expected: dispatch.actions.len() equals `2`
   - Expected: dispatch.actions[0] equals `inline-click`
   - Expected: dispatch.actions[1] equals `listener-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatches actions with event object state")
var button = BeDomNode.element("button")
button.set_attr("id", "save")
button.set_attr("onclick", "inline-click")
button.add_event_listener("click", "listener-a")

val index = _dom_event_index(button)
val route = _dom_event_route(index, button)
val dispatch = be_dom_dispatch_event_to_route(
    button, index, route, "onclick", true, true, true
)

expect(dispatch.event.event_type).to_equal("click")
expect(_dom_event_author_id(index, dispatch.target_route)).to_equal("save")
expect(dispatch.current_targets[0]).to_equal(route)
expect(dispatch.actions.len()).to_equal(2)
expect(dispatch.actions[0]).to_equal("inline-click")
expect(dispatch.actions[1]).to_equal("listener-a")
```

</details>

#### reports default actions for focused interactive element events

- reports default actions for focused interactive element events
   - Expected: link_dispatch.default_action equals `navigate:/next`
   - Expected: link_dispatch.default_action_allowed is true
   - Expected: checkbox_dispatch.default_action equals `input-checkbox-toggle`
   - Expected: checkbox_dispatch.default_action_allowed is true
   - Expected: form_dispatch.default_action equals `form-submit`
   - Expected: form_dispatch.default_action_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports default actions for focused interactive element events")
var link = BeDomNode.element("a")
link.set_attr("href", "/next")
val link_index = _dom_event_index(link)
val link_dispatch = be_dom_dispatch_event_to_route(
    link, link_index, _dom_event_route(link_index, link),
    "click", true, true, true
)
expect(link_dispatch.default_action).to_equal("navigate:/next")
expect(link_dispatch.default_action_allowed).to_equal(true)

var checkbox = BeDomNode.element("input")
checkbox.set_attr("type", "checkbox")
val checkbox_index = _dom_event_index(checkbox)
val checkbox_dispatch = be_dom_dispatch_event_to_route(
    checkbox, checkbox_index,
    _dom_event_route(checkbox_index, checkbox),
    "click", true, true, true
)
expect(checkbox_dispatch.default_action).to_equal("input-checkbox-toggle")
expect(checkbox_dispatch.default_action_allowed).to_equal(true)

var form = BeDomNode.element("form")
val form_index = _dom_event_index(form)
val form_dispatch = be_dom_dispatch_event_to_route(
    form, form_index, _dom_event_route(form_index, form),
    "submit", true, true, true
)
expect(form_dispatch.default_action).to_equal("form-submit")
expect(form_dispatch.default_action_allowed).to_equal(true)
```

</details>

#### suppresses cancelable default actions when a listener prevents default

- suppresses cancelable default actions when a listener prevents default
   - Expected: dispatch.event.default_prevented is true
   - Expected: dispatch.default_action equals `navigate:/blocked`
   - Expected: dispatch.default_action_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("suppresses cancelable default actions when a listener prevents default")
var link = BeDomNode.element("a")
link.set_attr("href", "/blocked")
link.add_event_listener("click", "prevent-default")

val index = _dom_event_index(link)
val dispatch = be_dom_dispatch_event_to_route(
    link, index, _dom_event_route(index, link),
    "click", true, true, true
)

expect(dispatch.event.default_prevented).to_equal(true)
expect(dispatch.default_action).to_equal("navigate:/blocked")
expect(dispatch.default_action_allowed).to_equal(false)
```

</details>

#### keeps non-cancelable default actions allowed despite prevent-default token

- keeps non-cancelable default actions allowed despite prevent-default token
   - Expected: dispatch.event.default_prevented is false
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: dispatch.default_action_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps non-cancelable default actions allowed despite prevent-default token")
var button = BeDomNode.element("button")
button.add_event_listener("click", "prevent-default")

val index = _dom_event_index(button)
val dispatch = be_dom_dispatch_event_to_route(
    button, index, _dom_event_route(index, button),
    "click", true, false, true
)

expect(dispatch.event.default_prevented).to_equal(false)
expect(dispatch.default_action).to_equal("button-activate")
expect(dispatch.default_action_allowed).to_equal(true)
```

</details>

#### applies allowed checkbox and radio default actions to returned nodes

- applies allowed checkbox and radio default actions to returned nodes
   - Expected: be_dom_has_attr(checked, "checked") is true
   - Expected: be_dom_has_attr(unchecked, "checked") is false
   - Expected: be_dom_has_attr(selected, "checked") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies allowed checkbox and radio default actions to returned nodes")
var checkbox = BeDomNode.element("input")
checkbox.set_attr("type", "checkbox")

val checkbox_index = _dom_event_index(checkbox)
val checkbox_route = _dom_event_route(checkbox_index, checkbox)
val checkbox_dispatch = be_dom_dispatch_event_to_route(
    checkbox, checkbox_index, checkbox_route,
    "click", true, true, true
)
val checked = be_dom_apply_default_action_to_route(
    checkbox, checkbox_index, checkbox_route,
    checkbox_dispatch.default_action
)
expect(be_dom_has_attr(checked, "checked")).to_equal(true)

val checked_index = _dom_event_index(checked)
val checked_route = _dom_event_route(checked_index, checked)
val checked_dispatch = be_dom_dispatch_event_to_route(
    checked, checked_index, checked_route,
    "click", true, true, true
)
val unchecked = be_dom_apply_default_action_to_route(
    checked, checked_index, checked_route,
    checked_dispatch.default_action
)
expect(be_dom_has_attr(unchecked, "checked")).to_equal(false)

var radio = BeDomNode.element("input")
radio.set_attr("type", "radio")
val radio_index = _dom_event_index(radio)
val radio_route = _dom_event_route(radio_index, radio)
val radio_dispatch = be_dom_dispatch_event_to_route(
    radio, radio_index, radio_route,
    "click", true, true, true
)
val selected = be_dom_apply_default_action_to_route(
    radio, radio_index, radio_route, radio_dispatch.default_action
)
expect(be_dom_has_attr(selected, "checked")).to_equal(true)
```

</details>

#### does not apply prevented or disabled control default actions

- does not apply prevented or disabled control default actions
   - Expected: be_dom_has_attr(still_unchecked, "checked") is false
   - Expected: dispatch.actions.len() equals `0`
   - Expected: dispatch.default_action equals ``
   - Expected: dispatch.default_action_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not apply prevented or disabled control default actions")
var prevented = BeDomNode.element("input")
prevented.set_attr("type", "checkbox")
prevented.add_event_listener("click", "prevent-default")

val prevented_index = _dom_event_index(prevented)
val prevented_route = _dom_event_route(prevented_index, prevented)
val prevented_dispatch = be_dom_dispatch_event_to_route(
    prevented, prevented_index, prevented_route,
    "click", true, true, true
)
val still_unchecked = if prevented_dispatch.default_action_allowed:
    be_dom_apply_default_action_to_route(
        prevented, prevented_index, prevented_route,
        prevented_dispatch.default_action
    )
else:
    prevented
expect(be_dom_has_attr(still_unchecked, "checked")).to_equal(false)

var disabled = BeDomNode.element("button")
disabled.set_attr("disabled", "disabled")
disabled.add_event_listener("click", "set-attr:data-clicked=true")
val disabled_index = _dom_event_index(disabled)
val dispatch = be_dom_dispatch_event_to_route(
    disabled, disabled_index,
    _dom_event_route(disabled_index, disabled),
    "click", true, true, true
)
expect(dispatch.actions.len()).to_equal(0)
expect(dispatch.default_action).to_equal("")
expect(dispatch.default_action_allowed).to_equal(false)
```

</details>

#### applies focus submit button and navigation default action tokens

- applies focus submit button and navigation default action tokens
   - Expected: be_dom_get_attr(focused, "data-focused") equals `true`
   - Expected: be_dom_get_attr(activated, "data-activated") equals `true`
   - Expected: be_dom_get_attr(submitted, "data-submitted") equals `true`
   - Expected: be_dom_get_attr(navigated, "data-navigation") equals `/next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies focus submit button and navigation default action tokens")
var input = BeDomNode.element("input")
val focused = be_dom_apply_default_action(input, "focus-element")
expect(be_dom_get_attr(focused, "data-focused")).to_equal("true")

var button = BeDomNode.element("button")
val activated = be_dom_apply_default_action(button, "button-activate")
expect(be_dom_get_attr(activated, "data-activated")).to_equal("true")

var form = BeDomNode.element("form")
val submitted = be_dom_apply_default_action(form, "form-submit")
expect(be_dom_get_attr(submitted, "data-submitted")).to_equal("true")

var link = BeDomNode.element("a")
val navigated = be_dom_apply_default_action(link, "navigate:/next")
expect(be_dom_get_attr(navigated, "data-navigation")).to_equal("/next")
```

</details>

#### maps focused keyboard activation keys to synthesized click events

- maps focused keyboard activation keys to synthesized click events
   - Expected: be_dom_keyboard_activation_event_for_target(link, "Enter") equals `click`
   - Expected: be_dom_keyboard_activation_event_for_target(link, "Space") equals ``
   - Expected: be_dom_keyboard_activation_event_for_target(button, "Return") equals `click`
   - Expected: be_dom_keyboard_activation_event_for_target(button, " ") equals `click`
   - Expected: be_dom_keyboard_activation_event_for_target(checkbox, "spacebar") equals `click`
   - Expected: be_dom_keyboard_activation_event_for_target(disabled, "Enter") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps focused keyboard activation keys to synthesized click events")
var link = BeDomNode.element("a")
link.set_attr("href", "/next")
expect(be_dom_keyboard_activation_event_for_target(link, "Enter")).to_equal("click")
expect(be_dom_keyboard_activation_event_for_target(link, "Space")).to_equal("")

var button = BeDomNode.element("button")
expect(be_dom_keyboard_activation_event_for_target(button, "Return")).to_equal("click")
expect(be_dom_keyboard_activation_event_for_target(button, " ")).to_equal("click")

var checkbox = BeDomNode.element("input")
checkbox.set_attr("type", "checkbox")
expect(be_dom_keyboard_activation_event_for_target(checkbox, "spacebar")).to_equal("click")

var submit = BeDomNode.element("input")
submit.set_attr("type", "submit")
expect(be_dom_keyboard_activation_event_for_target(
    submit, "Space"
)).to_equal("click")

var disabled = BeDomNode.element("button")
disabled.set_attr("disabled", "disabled")
expect(be_dom_keyboard_activation_event_for_target(disabled, "Enter")).to_equal("")
```

</details>

#### applies keyboard activation defaults to returned nodes

- applies keyboard activation defaults to returned nodes
   - Expected: be_dom_has_attr(checked, "checked") is true
   - Expected: be_dom_get_attr(navigated, "data-navigation") equals `/next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies keyboard activation defaults to returned nodes")
var checkbox = BeDomNode.element("input")
checkbox.set_attr("type", "checkbox")

val checkbox_index = _dom_event_index(checkbox)
val checkbox_route = _dom_event_route(checkbox_index, checkbox)
val checkbox_dispatch = be_dom_dispatch_event_to_route(
    checkbox, checkbox_index, checkbox_route,
    be_dom_keyboard_activation_event_for_target(checkbox, "Space"),
    true, true, true
)
val checked = be_dom_apply_default_action_to_route(
    checkbox, checkbox_index, checkbox_route,
    checkbox_dispatch.default_action
)
expect(be_dom_has_attr(checked, "checked")).to_equal(true)

var link = BeDomNode.element("a")
link.set_attr("href", "/next")
val link_index = _dom_event_index(link)
val link_route = _dom_event_route(link_index, link)
val link_dispatch = be_dom_dispatch_event_to_route(
    link, link_index, link_route,
    be_dom_keyboard_activation_event_for_target(link, "Enter"),
    true, true, true
)
val navigated = be_dom_apply_default_action_to_route(
    link, link_index, link_route, link_dispatch.default_action
)
expect(be_dom_get_attr(navigated, "data-navigation")).to_equal("/next")
```

</details>

#### stops same-target listener dispatch immediately

- stops same-target listener dispatch immediately
   - Expected: dispatch.event.propagation_stopped is true
   - Expected: dispatch.event.immediate_propagation_stopped is true
   - Expected: dispatch.actions.len() equals `2`
   - Expected: dispatch.actions[0] equals `listener-before`
   - Expected: dispatch.actions[1] equals `stop-immediate-propagation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stops same-target listener dispatch immediately")
var button = BeDomNode.element("button")
button.add_event_listener("click", "listener-before")
button.add_event_listener("click", "stop-immediate-propagation")
button.add_event_listener("click", "listener-after")

val index = _dom_event_index(button)
val dispatch = be_dom_dispatch_event_to_route(
    button, index, _dom_event_route(index, button),
    "click", true, true, true
)

expect(dispatch.event.propagation_stopped).to_equal(true)
expect(dispatch.event.immediate_propagation_stopped).to_equal(true)
expect(dispatch.actions.len()).to_equal(2)
expect(dispatch.actions[0]).to_equal("listener-before")
expect(dispatch.actions[1]).to_equal("stop-immediate-propagation")
```

</details>

#### dispatches capture target and bubble phases along an explicit event path

- dispatches capture target and bubble phases along an explicit event path
   - Expected: _dom_event_author_id(index, dispatch.target_route) equals `save`
   - Expected: dispatch.actions.len() equals `6`
   - Expected: dispatch.actions[0] equals `root-capture`
   - Expected: dispatch.phases[0] equals `capture`
   - Expected: dispatch.actions[1] equals `section-capture`
   - Expected: dispatch.phases[1] equals `capture`
   - Expected: dispatch.actions[2] equals `inline-click`
   - Expected: dispatch.phases[2] equals `target`
   - Expected: dispatch.actions[3] equals `target-listener`
   - Expected: dispatch.phases[3] equals `target`
   - Expected: dispatch.actions[4] equals `section-bubble`
   - Expected: dispatch.phases[4] equals `bubble`
   - Expected: dispatch.actions[5] equals `root-bubble`
   - Expected: dispatch.phases[5] equals `bubble`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatches capture target and bubble phases along an explicit event path")
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_event_listener_with_capture("click", "root-capture", true)
root.add_event_listener("click", "root-bubble")
var section = BeDomNode.element("section")
section.set_attr("id", "section")
section.add_event_listener_with_capture("click", "section-capture", true)
section.add_event_listener("click", "section-bubble")
var button = BeDomNode.element("button")
button.set_attr("id", "save")
button.set_attr("onclick", "inline-click")
button.add_event_listener("click", "target-listener")
section.add_child(button)
root.add_child(section)

val index = _dom_event_index(root)
val route = index.route_for_author_id("save").unwrap()
val dispatch = be_dom_dispatch_event_to_route(
    root, index, route, "click", true, true, true
)

expect(_dom_event_author_id(index, dispatch.target_route)).to_equal("save")
expect(dispatch.actions.len()).to_equal(6)
expect(dispatch.actions[0]).to_equal("root-capture")
expect(dispatch.phases[0]).to_equal("capture")
expect(dispatch.actions[1]).to_equal("section-capture")
expect(dispatch.phases[1]).to_equal("capture")
expect(dispatch.actions[2]).to_equal("inline-click")
expect(dispatch.phases[2]).to_equal("target")
expect(dispatch.actions[3]).to_equal("target-listener")
expect(dispatch.phases[3]).to_equal("target")
expect(dispatch.actions[4]).to_equal("section-bubble")
expect(dispatch.phases[4]).to_equal("bubble")
expect(dispatch.actions[5]).to_equal("root-bubble")
expect(dispatch.phases[5]).to_equal("bubble")
```

</details>

#### runs target capture listeners before inline and bubble listeners

- runs target capture listeners before inline and bubble listeners
   - Expected: dispatch.actions.len() equals `5`
   - Expected: dispatch.actions[0] equals `capture-second`
   - Expected: dispatch.actions[1] equals `stop-propagation`
   - Expected: dispatch.actions[2] equals `inline-click`
   - Expected: dispatch.actions[3] equals `bubble-first`
   - Expected: dispatch.actions[4] equals `bubble-third`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs target capture listeners before inline and bubble listeners")
var button = BeDomNode.element("button")
button.set_attr("id", "save")
button.set_attr("onclick", "inline-click")
button.add_event_listener("click", "bubble-first")
button.add_event_listener_with_capture(
    "click", "capture-second", true
)
button.add_event_listener_with_capture(
    "click", "stop-propagation", true
)
button.add_event_listener("click", "bubble-third")

val index = _dom_event_index(button)
val dispatch = be_dom_dispatch_event_to_route(
    button, index, _dom_event_route(index, button),
    "click", true, true, true
)

expect(dispatch.actions.len()).to_equal(5)
expect(dispatch.actions[0]).to_equal("capture-second")
expect(dispatch.actions[1]).to_equal("stop-propagation")
expect(dispatch.actions[2]).to_equal("inline-click")
expect(dispatch.actions[3]).to_equal("bubble-first")
expect(dispatch.actions[4]).to_equal("bubble-third")
```

</details>

#### stops propagation from capture before reaching target or bubble listeners

- stops propagation from capture before reaching target or bubble listeners
   - Expected: dispatch.event.propagation_stopped is true
   - Expected: dispatch.event.immediate_propagation_stopped is false
   - Expected: dispatch.actions.len() equals `4`
   - Expected: dispatch.actions[0] equals `root-capture`
   - Expected: dispatch.actions[1] equals `section-capture`
   - Expected: dispatch.actions[2] equals `stop-propagation`
   - Expected: dispatch.actions[3] equals `section-capture-after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stops propagation from capture before reaching target or bubble listeners")
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_event_listener_with_capture("click", "root-capture", true)
var section = BeDomNode.element("section")
section.set_attr("id", "section")
section.add_event_listener_with_capture("click", "section-capture", true)
section.add_event_listener_with_capture("click", "stop-propagation", true)
section.add_event_listener_with_capture("click", "section-capture-after", true)
section.add_event_listener("click", "section-bubble")
var button = BeDomNode.element("button")
button.set_attr("id", "save")
button.add_event_listener("click", "target-listener")
section.add_child(button)
root.add_child(section)

val index = _dom_event_index(root)
val dispatch = be_dom_dispatch_event_to_route(
    root, index, index.route_for_author_id("save").unwrap(),
    "click", true, true, true
)

expect(dispatch.event.propagation_stopped).to_equal(true)
expect(dispatch.event.immediate_propagation_stopped).to_equal(false)
expect(dispatch.actions.len()).to_equal(4)
expect(dispatch.actions[0]).to_equal("root-capture")
expect(dispatch.actions[1]).to_equal("section-capture")
expect(dispatch.actions[2]).to_equal("stop-propagation")
expect(dispatch.actions[3]).to_equal("section-capture-after")
```

</details>

#### keeps the target default action after propagation is stopped

- keeps the target default action after propagation is stopped
   - Expected: dispatch.default_action equals `input-checkbox-toggle`
   - Expected: dispatch.default_action_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the target default action after propagation is stopped")
var root = BeDomNode.element("main")
root.add_event_listener_with_capture("click", "stop-propagation", true)
var checkbox = BeDomNode.element("input")
checkbox.set_attr("type", "checkbox")
root.add_child(checkbox)

val index = _dom_event_index(root)
val dispatch = be_dom_dispatch_event_to_route(
    root, index,
    DomNodeRoute(
        generation: index.generation, node_id: checkbox.node_id
    ),
    "click", true, true, true
)

expect(dispatch.default_action).to_equal("input-checkbox-toggle")
expect(dispatch.default_action_allowed).to_equal(true)
```

</details>

#### does not run ancestor bubble listeners for non-bubbling events

- does not run ancestor bubble listeners for non-bubbling events
   - Expected: dispatch.actions.len() equals `2`
   - Expected: dispatch.actions[0] equals `root-capture`
   - Expected: dispatch.phases[0] equals `capture`
   - Expected: dispatch.actions[1] equals `target-focus`
   - Expected: dispatch.phases[1] equals `target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not run ancestor bubble listeners for non-bubbling events")
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_event_listener_with_capture("focus", "root-capture", true)
root.add_event_listener("focus", "root-bubble")
var input = BeDomNode.element("input")
input.set_attr("id", "name")
input.add_event_listener("focus", "target-focus")
root.add_child(input)

val index = _dom_event_index(root)
val dispatch = be_dom_dispatch_event_to_route(
    root, index, index.route_for_author_id("name").unwrap(),
    "focus", false, false, true
)

expect(dispatch.actions.len()).to_equal(2)
expect(dispatch.actions[0]).to_equal("root-capture")
expect(dispatch.phases[0]).to_equal("capture")
expect(dispatch.actions[1]).to_equal("target-focus")
expect(dispatch.phases[1]).to_equal("target")
```

</details>

#### finds a root to target path by element id

- finds a root to target path by element id
   - Expected: path.len() equals `3`
   - Expected: path[0].id equals `root`
   - Expected: path[1].id equals `section`
   - Expected: path[2].id equals `save`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds a root to target path by element id")
var button = BeDomNode.element("button")
button.set_attr("id", "save")
var section = BeDomNode.element("section")
section.set_attr("id", "section")
section.add_child(button)
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_child(section)

val index = _dom_event_index(root)
val path = be_dom_path_for_route(
    root, index, index.route_for_author_id("save").unwrap()
)

expect(path.len()).to_equal(3)
expect(path[0].id).to_equal("root")
expect(path[1].id).to_equal("section")
expect(path[2].id).to_equal("save")
```

</details>

#### dispatches capture target and bubble phases by target id

- dispatches capture target and bubble phases by target id
   - Expected: _dom_event_author_id(index, dispatch.target_route) equals `save`
   - Expected: dispatch.actions.len() equals `6`
   - Expected: dispatch.actions[0] equals `root-capture`
   - Expected: dispatch.actions[1] equals `section-capture`
   - Expected: dispatch.actions[2] equals `inline-click`
   - Expected: dispatch.actions[3] equals `target-listener`
   - Expected: dispatch.actions[4] equals `section-bubble`
   - Expected: dispatch.actions[5] equals `root-bubble`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatches capture target and bubble phases by target id")
var button = BeDomNode.element("button")
button.set_attr("id", "save")
button.set_attr("onclick", "inline-click")
button.add_event_listener("click", "target-listener")
var section = BeDomNode.element("section")
section.set_attr("id", "section")
section.add_event_listener_with_capture("click", "section-capture", true)
section.add_event_listener("click", "section-bubble")
section.add_child(button)
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_event_listener_with_capture("click", "root-capture", true)
root.add_event_listener("click", "root-bubble")
root.add_child(section)

val index = _dom_event_index(root)
val dispatch = be_dom_dispatch_event_to_route(
    root, index, index.route_for_author_id("save").unwrap(),
    "onclick", true, true, true
)

expect(_dom_event_author_id(index, dispatch.target_route)).to_equal("save")
expect(dispatch.actions.len()).to_equal(6)
expect(dispatch.actions[0]).to_equal("root-capture")
expect(dispatch.actions[1]).to_equal("section-capture")
expect(dispatch.actions[2]).to_equal("inline-click")
expect(dispatch.actions[3]).to_equal("target-listener")
expect(dispatch.actions[4]).to_equal("section-bubble")
expect(dispatch.actions[5]).to_equal("root-bubble")
```

</details>

#### returns an empty dispatch when target id is not found

- returns an empty dispatch when target id is not found
   - Expected: dispatch.target_route equals `missing`
   - Expected: dispatch.actions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns an empty dispatch when target id is not found")
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_event_listener_with_capture("click", "root-capture", true)

val index = _dom_event_index(root)
val missing = DomNodeRoute(
    generation: index.generation, node_id: 9223372036854775807
)
val dispatch = be_dom_dispatch_event_to_route(
    root, index, missing, "click", true, true, true
)

expect(dispatch.target_route).to_equal(missing)
expect(index.author_id_for_route(dispatch.target_route)).to_be_nil()
expect(dispatch.actions.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser renderer DOM event basics.
- Browser renderer DOM event basics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c92ca18668b10b56950e192266618e2fb87e8158f8c1ce232f1dfc4d750721a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c92ca18668b10b56950e192266618e2fb87e8158f8c1ce232f1dfc4d750721a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c92ca18668b10b56950e192266618e2fb87e8158f8c1ce232f1dfc4d750721a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 27 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers target event listeners with normalized event names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses removed listener tombstones without growing the registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes listener control through the canonical dispatch cursor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
