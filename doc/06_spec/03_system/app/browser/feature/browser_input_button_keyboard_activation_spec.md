# Hosted input-button keyboard activation

Status: **DRAFT / EVIDENCE-BLOCKED**

Executable source:
`test/03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.spl`.
No runtime result is claimed until an admitted current pure-Simple runner
executes the scenario.

## Scope and production route

Native `<input type="button">` controls must remain operable by keyboard and
pointer without becoming form submitters. The executable drives the production
`HostedWebContentSession` APIs used by `hosted_entry`:

```text
host key
  -> dispatch_key_with_shift
  -> BrowserSession.dispatch_dom_keyboard_code_event
  -> be_dom_keyboard_activation_event_for_target
  -> click

host pointer
  -> dispatch_pointer_at
  -> pointerdown / mousedown / pointerup / mouseup / click
```

The implementation change is limited to classifying Enter and Space on an
input whose exact type is `button` as click activation. Existing Space timing
arms on key-down and clicks on key-up; existing Enter timing clicks on
key-down. Existing form-owner checks continue to reject `type=button` as a
submitter.

## Scenario: preserve keyboard pointer and form semantics

### 1. Install hosted input-button activation controls

`setup_hosted_input_button_activation_fixture` creates hosted window `802`
with a guarded POST form targeting
`https://must-not-submit.test/save` and three block-layout input buttons:

- `space-button`;
- `enter-button`;
- `pointer-button`.

Each control records exact focus, blur, or click attributes. The form records
`data-submit=yes` if a submit event is incorrectly dispatched. The fixed
20-pixel block geometry gives the pointer control the exact test point
`(5, 45)`.

### 2. Focus input buttons through the host Tab route

`focus_input_buttons_through_host_tab` sends Tab down/up through
`dispatch_key_with_shift`.

Exact oracles:

- key-down semantic target is `space-button`;
- key-down callback count is `1` for its focus listener;
- key-up retains `space-button` and has callback count `0`;
- DOM focus is exactly `space-button`;
- `data-focus="space"` is present.

### 3. Activate the focused controls with Space and Enter

`activate_input_buttons_through_host_keyboard` sends both key edges through
the same hosted route.

Space oracles:

- key-down targets `space-button`, has callback count `0`, and does not expose
  `data-click="space"`;
- key-up targets `space-button`, has callback count `1`, and exposes the click
  attribute;
- pending form-request count remains `0` on both edges.

A hosted Tab transition then targets `enter-button`, has callback count `2`
for the old control's blur and new control's focus, and records both exact
attributes.

Enter oracles:

- key-down targets `enter-button`, has callback count `1`, and exposes
  `data-click="enter"`;
- key-up retains the target and has callback count `0`;
- pending form-request count remains `0` on both edges.

### 4. Preserve pointer parity and form non-submission

`check_input_button_activation_and_form_safety` presses and releases `(5, 45)`
through `dispatch_pointer_at`.

Exact oracles:

- pointer-down targets `pointer-button`, has callback count `2` for blur and
  focus, records `data-blur="enter"` and `data-focus="pointer"`, and has not
  clicked yet;
- pointer-up targets the same button, has callback count `1`, and records
  `data-click="pointer"`;
- `data-submit="yes"` is absent;
- pending form-request count is exactly `0`.

## Frozen helper and step parity

Helpers:

- `setup_hosted_input_button_activation_fixture`
- `focus_input_buttons_through_host_tab`
- `activate_input_buttons_through_host_keyboard`
- `check_input_button_activation_and_form_safety`

Visible steps:

1. `Install hosted input-button activation controls`
2. `Focus input buttons through the host Tab route`
3. `Activate the focused controls with Space and Enter`
4. `Preserve pointer parity and form non-submission`
