# Browser Renderer Dom Events Specification

> 1. var button = BeDomNode element

<!-- sdn-diagram:id=browser_renderer_dom_events_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_renderer_dom_events_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_renderer_dom_events_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_renderer_dom_events_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Dom Events Specification

## Scenarios

### Browser renderer DOM event basics

#### registers target event listeners with normalized event names

1. var button = BeDomNode element
2. button add event listener
3. button add event listener
   - Expected: be_dom_get_event_listener_count(button, "click") equals `2`
   - Expected: be_dom_get_event_listener_count(button, "onclick") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var button = BeDomNode.element("button")
button.add_event_listener("click", "listener-a")
button.add_event_listener("onclick", "listener-b")

expect(be_dom_get_event_listener_count(button, "click")).to_equal(2)
expect(be_dom_get_event_listener_count(button, "onclick")).to_equal(2)
```

</details>

#### dispatches inline handlers before registered target listeners

1. var button = BeDomNode element
2. button set attr
3. button add event listener
4. button add event listener
   - Expected: actions.len() equals `3`
   - Expected: actions[0] equals `inline-click`
   - Expected: actions[1] equals `listener-a`
   - Expected: actions[2] equals `listener-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var input = BeDomNode element
2. input add event listener
3. input add event listener
   - Expected: input_actions.len() equals `1`
   - Expected: input_actions[0] equals `input-listener`
   - Expected: change_actions.len() equals `1`
   - Expected: change_actions[0] equals `change-listener`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### creates cancelable event objects with target and current target state

1. var button = BeDomNode element
2. button set attr
3. var event = be dom create event
   - Expected: event.event_type equals `click`
   - Expected: event.target_tag equals `button`
   - Expected: event.target_id equals `save`
   - Expected: event.current_target_tag equals `button`
   - Expected: event.current_target_id equals `save`
   - Expected: event.bubbles is true
   - Expected: event.cancelable is true
   - Expected: event.default_prevented is false
4. event prevent default
   - Expected: event.default_prevented is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var button = BeDomNode.element("button")
button.set_attr("id", "save")

var event = be_dom_create_event(button, "onclick", true, true)
expect(event.event_type).to_equal("click")
expect(event.target_tag).to_equal("button")
expect(event.target_id).to_equal("save")
expect(event.current_target_tag).to_equal("button")
expect(event.current_target_id).to_equal("save")
expect(event.bubbles).to_equal(true)
expect(event.cancelable).to_equal(true)
expect(event.default_prevented).to_equal(false)

event.prevent_default()
expect(event.default_prevented).to_equal(true)
```

</details>

#### creates pointer events with basic mouse payload fields

1. var button = BeDomNode element
2. button set attr
   - Expected: event.event_type equals `mousedown`
   - Expected: event.target_id equals `save`
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

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var button = BeDomNode.element("button")
button.set_attr("id", "save")

val event = be_dom_create_pointer_event(button, "mousedown", true, true, 12, 34, 0, 1, 0)

expect(event.event_type).to_equal("mousedown")
expect(event.target_id).to_equal("save")
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

1. var button = BeDomNode element
2. button set attr
   - Expected: event.event_type equals `click`
   - Expected: event.target_id equals `save`
   - Expected: event.alt_key is true
   - Expected: event.ctrl_key is false
   - Expected: event.meta_key is true
   - Expected: event.shift_key is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var button = BeDomNode.element("button")
button.set_attr("id", "save")

val event = be_dom_create_pointer_event_with_modifiers(button, "click", true, true, 12, 34, 0, 0, 1, true, false, true, true)

expect(event.event_type).to_equal("click")
expect(event.target_id).to_equal("save")
expect(event.alt_key).to_equal(true)
expect(event.ctrl_key).to_equal(false)
expect(event.meta_key).to_equal(true)
expect(event.shift_key).to_equal(true)
```

</details>

#### leaves non-cancelable events unprevented

1. var link = BeDomNode element
2. var event = be dom create event
3. event prevent default
   - Expected: event.default_prevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var link = BeDomNode.element("a")
var event = be_dom_create_event(link, "click", true, false)

event.prevent_default()

expect(event.default_prevented).to_equal(false)
```

</details>

#### dispatches actions with event object state

1. var button = BeDomNode element
2. button set attr
3. button set attr
4. button add event listener
   - Expected: dispatch.event.event_type equals `click`
   - Expected: dispatch.event.target_id equals `save`
   - Expected: dispatch.event.current_target_id equals `save`
   - Expected: dispatch.actions.len() equals `2`
   - Expected: dispatch.actions[0] equals `inline-click`
   - Expected: dispatch.actions[1] equals `listener-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var button = BeDomNode.element("button")
button.set_attr("id", "save")
button.set_attr("onclick", "inline-click")
button.add_event_listener("click", "listener-a")

val dispatch = be_dom_dispatch_event(button, "onclick", true, true)

expect(dispatch.event.event_type).to_equal("click")
expect(dispatch.event.target_id).to_equal("save")
expect(dispatch.event.current_target_id).to_equal("save")
expect(dispatch.actions.len()).to_equal(2)
expect(dispatch.actions[0]).to_equal("inline-click")
expect(dispatch.actions[1]).to_equal("listener-a")
```

</details>

#### reports default actions for focused interactive element events

1. var link = BeDomNode element
2. link set attr
   - Expected: link_dispatch.default_action equals `navigate:/next`
   - Expected: link_dispatch.default_action_allowed is true
3. var checkbox = BeDomNode element
4. checkbox set attr
   - Expected: checkbox_dispatch.default_action equals `input-checkbox-toggle`
   - Expected: checkbox_dispatch.default_action_allowed is true
5. var form = BeDomNode element
   - Expected: form_dispatch.default_action equals `form-submit`
   - Expected: form_dispatch.default_action_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var link = BeDomNode.element("a")
link.set_attr("href", "/next")
val link_dispatch = be_dom_dispatch_event(link, "click", true, true)
expect(link_dispatch.default_action).to_equal("navigate:/next")
expect(link_dispatch.default_action_allowed).to_equal(true)

var checkbox = BeDomNode.element("input")
checkbox.set_attr("type", "checkbox")
val checkbox_dispatch = be_dom_dispatch_event(checkbox, "click", true, true)
expect(checkbox_dispatch.default_action).to_equal("input-checkbox-toggle")
expect(checkbox_dispatch.default_action_allowed).to_equal(true)

var form = BeDomNode.element("form")
val form_dispatch = be_dom_dispatch_event(form, "submit", true, true)
expect(form_dispatch.default_action).to_equal("form-submit")
expect(form_dispatch.default_action_allowed).to_equal(true)
```

</details>

#### suppresses cancelable default actions when a listener prevents default

1. var link = BeDomNode element
2. link set attr
3. link add event listener
   - Expected: dispatch.event.default_prevented is true
   - Expected: dispatch.default_action equals `navigate:/blocked`
   - Expected: dispatch.default_action_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var link = BeDomNode.element("a")
link.set_attr("href", "/blocked")
link.add_event_listener("click", "prevent-default")

val dispatch = be_dom_dispatch_event(link, "click", true, true)

expect(dispatch.event.default_prevented).to_equal(true)
expect(dispatch.default_action).to_equal("navigate:/blocked")
expect(dispatch.default_action_allowed).to_equal(false)
```

</details>

#### keeps non-cancelable default actions allowed despite prevent-default token

1. var button = BeDomNode element
2. button add event listener
   - Expected: dispatch.event.default_prevented is false
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: dispatch.default_action_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var button = BeDomNode.element("button")
button.add_event_listener("click", "prevent-default")

val dispatch = be_dom_dispatch_event(button, "click", true, false)

expect(dispatch.event.default_prevented).to_equal(false)
expect(dispatch.default_action).to_equal("button-activate")
expect(dispatch.default_action_allowed).to_equal(true)
```

</details>

#### applies allowed checkbox and radio default actions to returned nodes

1. var checkbox = BeDomNode element
2. checkbox set attr
   - Expected: be_dom_has_attr(checked, "checked") is true
   - Expected: be_dom_has_attr(unchecked, "checked") is false
3. var radio = BeDomNode element
4. radio set attr
   - Expected: be_dom_has_attr(selected, "checked") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var checkbox = BeDomNode.element("input")
checkbox.set_attr("type", "checkbox")

val checked = be_dom_dispatch_event_apply_default(checkbox, "click", true, true)
expect(be_dom_has_attr(checked, "checked")).to_equal(true)

val unchecked = be_dom_dispatch_event_apply_default(checked, "click", true, true)
expect(be_dom_has_attr(unchecked, "checked")).to_equal(false)

var radio = BeDomNode.element("input")
radio.set_attr("type", "radio")
val selected = be_dom_dispatch_event_apply_default(radio, "click", true, true)
expect(be_dom_has_attr(selected, "checked")).to_equal(true)
```

</details>

#### does not apply prevented or disabled control default actions

1. var prevented = BeDomNode element
2. prevented set attr
3. prevented add event listener
   - Expected: be_dom_has_attr(still_unchecked, "checked") is false
4. var disabled = BeDomNode element
5. disabled set attr
   - Expected: dispatch.default_action equals ``
   - Expected: dispatch.default_action_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var prevented = BeDomNode.element("input")
prevented.set_attr("type", "checkbox")
prevented.add_event_listener("click", "prevent-default")

val still_unchecked = be_dom_dispatch_event_apply_default(prevented, "click", true, true)
expect(be_dom_has_attr(still_unchecked, "checked")).to_equal(false)

var disabled = BeDomNode.element("button")
disabled.set_attr("disabled", "disabled")
val dispatch = be_dom_dispatch_event(disabled, "click", true, true)
expect(dispatch.default_action).to_equal("")
expect(dispatch.default_action_allowed).to_equal(false)
```

</details>

#### applies focus submit button and navigation default action tokens

1. var input = BeDomNode element
   - Expected: be_dom_get_attr(focused, "data-focused") equals `true`
2. var button = BeDomNode element
   - Expected: be_dom_get_attr(activated, "data-activated") equals `true`
3. var form = BeDomNode element
   - Expected: be_dom_get_attr(submitted, "data-submitted") equals `true`
4. var link = BeDomNode element
   - Expected: be_dom_get_attr(navigated, "data-navigation") equals `/next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var link = BeDomNode element
2. link set attr
   - Expected: be_dom_keyboard_activation_event_for_target(link, "Enter") equals `click`
   - Expected: be_dom_keyboard_activation_event_for_target(link, "Space") equals ``
3. var button = BeDomNode element
   - Expected: be_dom_keyboard_activation_event_for_target(button, "Return") equals `click`
   - Expected: be_dom_keyboard_activation_event_for_target(button, " ") equals `click`
4. var checkbox = BeDomNode element
5. checkbox set attr
   - Expected: be_dom_keyboard_activation_event_for_target(checkbox, "spacebar") equals `click`
6. var disabled = BeDomNode element
7. disabled set attr
   - Expected: be_dom_keyboard_activation_event_for_target(disabled, "Enter") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

var disabled = BeDomNode.element("button")
disabled.set_attr("disabled", "disabled")
expect(be_dom_keyboard_activation_event_for_target(disabled, "Enter")).to_equal("")
```

</details>

#### applies keyboard activation defaults to returned nodes

1. var checkbox = BeDomNode element
2. checkbox set attr
   - Expected: be_dom_has_attr(checked, "checked") is true
3. var link = BeDomNode element
4. link set attr
   - Expected: be_dom_get_attr(navigated, "data-navigation") equals `/next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var checkbox = BeDomNode.element("input")
checkbox.set_attr("type", "checkbox")

val checked = be_dom_dispatch_keyboard_activation_apply_default(checkbox, "Space")
expect(be_dom_has_attr(checked, "checked")).to_equal(true)

var link = BeDomNode.element("a")
link.set_attr("href", "/next")
val navigated = be_dom_dispatch_keyboard_activation_apply_default(link, "Enter")
expect(be_dom_get_attr(navigated, "data-navigation")).to_equal("/next")
```

</details>

#### stops same-target listener dispatch immediately

1. var button = BeDomNode element
2. button add event listener
3. button add event listener
4. button add event listener
   - Expected: dispatch.event.propagation_stopped is true
   - Expected: dispatch.event.immediate_propagation_stopped is true
   - Expected: dispatch.actions.len() equals `2`
   - Expected: dispatch.actions[0] equals `listener-before`
   - Expected: dispatch.actions[1] equals `stop-immediate-propagation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var button = BeDomNode.element("button")
button.add_event_listener("click", "listener-before")
button.add_event_listener("click", "stop-immediate-propagation")
button.add_event_listener("click", "listener-after")

val dispatch = be_dom_dispatch_event(button, "click", true, true)

expect(dispatch.event.propagation_stopped).to_equal(true)
expect(dispatch.event.immediate_propagation_stopped).to_equal(true)
expect(dispatch.actions.len()).to_equal(2)
expect(dispatch.actions[0]).to_equal("listener-before")
expect(dispatch.actions[1]).to_equal("stop-immediate-propagation")
```

</details>

#### dispatches capture target and bubble phases along an explicit event path

1. var root = BeDomNode element
2. root set attr
3. root add event listener with capture
4. root add event listener
5. var section = BeDomNode element
6. section set attr
7. section add event listener with capture
8. section add event listener
9. var button = BeDomNode element
10. button set attr
11. button set attr
12. button add event listener
   - Expected: dispatch.event.target_id equals `save`
   - Expected: dispatch.actions.len() equals `6`
   - Expected: dispatch.actions[0] equals `root-capture`
   - Expected: dispatch.phases[0] equals `capture`
   - Expected: dispatch.current_target_ids[0] equals `root`
   - Expected: dispatch.actions[1] equals `section-capture`
   - Expected: dispatch.phases[1] equals `capture`
   - Expected: dispatch.current_target_ids[1] equals `section`
   - Expected: dispatch.actions[2] equals `inline-click`
   - Expected: dispatch.phases[2] equals `target`
   - Expected: dispatch.current_target_ids[2] equals `save`
   - Expected: dispatch.actions[3] equals `target-listener`
   - Expected: dispatch.phases[3] equals `target`
   - Expected: dispatch.current_target_ids[3] equals `save`
   - Expected: dispatch.actions[4] equals `section-bubble`
   - Expected: dispatch.phases[4] equals `bubble`
   - Expected: dispatch.current_target_ids[4] equals `section`
   - Expected: dispatch.actions[5] equals `root-bubble`
   - Expected: dispatch.phases[5] equals `bubble`
   - Expected: dispatch.current_target_ids[5] equals `root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

val dispatch = be_dom_dispatch_event_path([root, section, button], "click", true, true)

expect(dispatch.event.target_id).to_equal("save")
expect(dispatch.actions.len()).to_equal(6)
expect(dispatch.actions[0]).to_equal("root-capture")
expect(dispatch.phases[0]).to_equal("capture")
expect(dispatch.current_target_ids[0]).to_equal("root")
expect(dispatch.actions[1]).to_equal("section-capture")
expect(dispatch.phases[1]).to_equal("capture")
expect(dispatch.current_target_ids[1]).to_equal("section")
expect(dispatch.actions[2]).to_equal("inline-click")
expect(dispatch.phases[2]).to_equal("target")
expect(dispatch.current_target_ids[2]).to_equal("save")
expect(dispatch.actions[3]).to_equal("target-listener")
expect(dispatch.phases[3]).to_equal("target")
expect(dispatch.current_target_ids[3]).to_equal("save")
expect(dispatch.actions[4]).to_equal("section-bubble")
expect(dispatch.phases[4]).to_equal("bubble")
expect(dispatch.current_target_ids[4]).to_equal("section")
expect(dispatch.actions[5]).to_equal("root-bubble")
expect(dispatch.phases[5]).to_equal("bubble")
expect(dispatch.current_target_ids[5]).to_equal("root")
```

</details>

#### stops propagation from capture before reaching target or bubble listeners

1. var root = BeDomNode element
2. root set attr
3. root add event listener with capture
4. var section = BeDomNode element
5. section set attr
6. section add event listener with capture
7. section add event listener with capture
8. section add event listener with capture
9. section add event listener
10. var button = BeDomNode element
11. button set attr
12. button add event listener
   - Expected: dispatch.event.propagation_stopped is true
   - Expected: dispatch.event.immediate_propagation_stopped is false
   - Expected: dispatch.actions.len() equals `4`
   - Expected: dispatch.actions[0] equals `root-capture`
   - Expected: dispatch.actions[1] equals `section-capture`
   - Expected: dispatch.actions[2] equals `stop-propagation`
   - Expected: dispatch.actions[3] equals `section-capture-after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

val dispatch = be_dom_dispatch_event_path([root, section, button], "click", true, true)

expect(dispatch.event.propagation_stopped).to_equal(true)
expect(dispatch.event.immediate_propagation_stopped).to_equal(false)
expect(dispatch.actions.len()).to_equal(4)
expect(dispatch.actions[0]).to_equal("root-capture")
expect(dispatch.actions[1]).to_equal("section-capture")
expect(dispatch.actions[2]).to_equal("stop-propagation")
expect(dispatch.actions[3]).to_equal("section-capture-after")
```

</details>

#### does not run ancestor bubble listeners for non-bubbling events

1. var root = BeDomNode element
2. root set attr
3. root add event listener with capture
4. root add event listener
5. var input = BeDomNode element
6. input set attr
7. input add event listener
   - Expected: dispatch.actions.len() equals `2`
   - Expected: dispatch.actions[0] equals `root-capture`
   - Expected: dispatch.phases[0] equals `capture`
   - Expected: dispatch.actions[1] equals `target-focus`
   - Expected: dispatch.phases[1] equals `target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_event_listener_with_capture("focus", "root-capture", true)
root.add_event_listener("focus", "root-bubble")
var input = BeDomNode.element("input")
input.set_attr("id", "name")
input.add_event_listener("focus", "target-focus")

val dispatch = be_dom_dispatch_event_path([root, input], "focus", false, false)

expect(dispatch.actions.len()).to_equal(2)
expect(dispatch.actions[0]).to_equal("root-capture")
expect(dispatch.phases[0]).to_equal("capture")
expect(dispatch.actions[1]).to_equal("target-focus")
expect(dispatch.phases[1]).to_equal("target")
```

</details>

#### finds a root to target path by element id

1. var button = BeDomNode element
2. button set attr
3. var section = BeDomNode element
4. section set attr
5. section add child
6. var root = BeDomNode element
7. root set attr
8. root add child
   - Expected: path.len() equals `3`
   - Expected: path[0].id equals `root`
   - Expected: path[1].id equals `section`
   - Expected: path[2].id equals `save`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var button = BeDomNode.element("button")
button.set_attr("id", "save")
var section = BeDomNode.element("section")
section.set_attr("id", "section")
section.add_child(button)
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_child(section)

val path = be_dom_find_path_to_id(root, "save")

expect(path.len()).to_equal(3)
expect(path[0].id).to_equal("root")
expect(path[1].id).to_equal("section")
expect(path[2].id).to_equal("save")
```

</details>

#### dispatches capture target and bubble phases by target id

1. var button = BeDomNode element
2. button set attr
3. button set attr
4. button add event listener
5. var section = BeDomNode element
6. section set attr
7. section add event listener with capture
8. section add event listener
9. section add child
10. var root = BeDomNode element
11. root set attr
12. root add event listener with capture
13. root add event listener
14. root add child
   - Expected: dispatch.event.target_id equals `save`
   - Expected: dispatch.actions.len() equals `6`
   - Expected: dispatch.actions[0] equals `root-capture`
   - Expected: dispatch.actions[1] equals `section-capture`
   - Expected: dispatch.actions[2] equals `inline-click`
   - Expected: dispatch.actions[3] equals `target-listener`
   - Expected: dispatch.actions[4] equals `section-bubble`
   - Expected: dispatch.actions[5] equals `root-bubble`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

val dispatch = be_dom_dispatch_event_to_id(root, "save", "onclick", true, true)

expect(dispatch.event.target_id).to_equal("save")
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

1. var root = BeDomNode element
2. root set attr
3. root add event listener with capture
   - Expected: dispatch.event.target_id equals ``
   - Expected: dispatch.actions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = BeDomNode.element("main")
root.set_attr("id", "root")
root.add_event_listener_with_capture("click", "root-capture", true)

val dispatch = be_dom_dispatch_event_to_id(root, "missing", "click", true, true)

expect(dispatch.event.target_id).to_equal("")
expect(dispatch.actions.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser renderer DOM event basics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
