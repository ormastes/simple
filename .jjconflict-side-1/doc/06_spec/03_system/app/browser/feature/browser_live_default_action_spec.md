# Browser live default-action validation

Click listeners may change the activation target before default behavior runs.
The original checkbox/radio pre-activation is rolled back when its action no
longer matches, and only the action derived from the live routed node executes.
New browsing-context targets remain distinct from current-document navigation
and fail closed when popup authority or a popup host is unavailable.

## Scenario: route only the action derived from the live target

### 1. Install guarded link and submit controls

`setup_post_dispatch_activation_fixture` opens one document containing:

- a checkbox changed to submit;
- a checkbox changed to text;
- a checkbox changed to radio beside an initially checked radio;
- a submit input changed to checkbox;
- a link whose `href` changes; and
- a link removed from `document.body`.

Every mutable input records `input`, `change`, and `focus`; the submit form
records `submit`. These attributes are the exact event oracles.

### 2. Mutate activation state inside click listeners

`trigger_pointer_and_keyboard_mutation` uses `ui_access_snapshot`,
`ui_access_find_nodes`, and `ui_access_act` for every control:

- pointer: checkbox-to-submit, checkbox-to-radio, changed link;
- keyboard: checkbox-to-text with Space, submit-to-checkbox with Enter,
  removed link with Enter.

The click listeners mutate `type`, `href`, or tree membership before default
behavior.

### 3. Suppress stale navigation and form submission

`check_invalidated_default_actions` checks the complete matrix:

| Mutation | checked | input/change | focus | submit/navigation |
|---|---|---|---|---|
| checkbox → submit | absent | absent | present | one `/checkbox-submit` |
| checkbox → text | absent | absent | present | none |
| checkbox → radio | present; old radio cleared | present | present | none |
| submit → checkbox | present | present | present | none |
| changed `href` | N/A | N/A | N/A | live `/live-destination` only |
| removed link | target absent | N/A | N/A | none |

The executable attribute oracles are exact:

- `checkbox-submit`: `checked`, `data-input`, and `data-change` are `""`;
  `data-focus` is `"yes"`; its form `data-submit` is `"yes"`.
- `checkbox-text`: `checked`, `data-input`, and `data-change` are `""`;
  `data-focus` is `"yes"`.
- `checkbox-radio`: `checked` is `"checked"`; the old radio's `checked` is
  `""`; `data-input`, `data-change`, and `data-focus` are `"yes"`.
- `submit-checkbox`: `checked` is `"checked"` and `data-input`,
  `data-change`, and `data-focus` are `"yes"`.
- `route_for_author_id("removed-link")` is `nil` in the current identity index.

`pending_request_count()` is exactly `2`. The first consumed URL is
`https://example.test/checkbox-submit`; the second is
`https://example.test/live-destination`; the final count is `0`. No stale
destination or extra form request is accepted.

### 4. Preserve unchanged control activation

`check_live_default_action_control_case` drives an unchanged checkbox by
pointer and an unchanged link by keyboard through UI access. The checkbox is
checked (`checked == "checked"`), receives `data-input == "yes"`,
`data-change == "yes"`, and `data-focus == "yes"`. The pending count is
exactly `1`; consuming it yields
`https://example.test/control-link`.

## Scenario: never coerce a new target into the current document

### 1. Install whitespace, mixed-case, named, and keyword targets

`setup_target_context_fixture` commits real network documents with
`Content-Security-Policy: sandbox allow-top-navigation`. The matrix contains:

- new contexts: `target=" _self "`, mixed-case and exact `_BLANK`/`_blank`,
  and the colon-and-whitespace name `report: frame`;
- current contexts: mixed-case and exact `_SELF`/`_self`, exact `_parent`,
  exact `_top`, and empty target.

Only `report: frame` grants `allow-popups`, while no popup-context host is
installed. Every fixture starts at
`https://example.test/target-context`, title `Committed target fixture`,
one history entry, and index zero.

### 2. Preserve raw new-context names and classify exact keywords

The shared DOM default-action oracle must return exact distinct actions:

- whitespace-surrounded self:
  `navigate-popup:7: _self /next`;
- mixed/exact blank:
  `navigate-popup:6:_BLANK/next` and
  `navigate-popup:6:_blank/next`;
- colon-and-whitespace name:
  `navigate-popup:13:report: frame/next`;
- mixed/exact self, parent, top, and empty: `navigate:/next`.

The decimal length prefix separates the raw target from the URL without
interpreting colons or whitespace in either value. Only comparison with the
reserved HTML target keywords is case-insensitive, and no whitespace is
trimmed.

### 3. Activate whitespace and keyword targets by pointer and Enter

The scenario drives all links through `ui_access_snapshot`,
`ui_access_find_nodes`, and `ui_access_act`. Pointer and Enter are both used
across new-context and current-context targets, including whitespace-surrounded
self, mixed-case blank/self, parent, top, exact keywords, and empty target.

### 4. Fail popup attempts closed and preserve current-target behavior

`expect_target_context_unchanged` proves each blocked or unavailable popup has
zero pending requests, keeps the exact committed URL/title/body, retains one
history entry at index zero, and records the exact warning:

- no `allow-popups`: `CSP sandbox blocked popup`;
- popup allowed but no host: `popup-context-unavailable`.

`expect_current_target_navigation` proves mixed/exact self, parent, top, and
empty target each still queue exactly one `document` request for
`https://example.test/next`.

## Executable helper and oracle map

- `_open_live_default_fixture`: fails explicitly on document setup error.
- `_act_live_control`: requires one UI-access node and a successful action.
- `setup_target_context_fixture`: commits a real CSP-governed target document.
- `expect_target_context_unchanged`: checks request, page, history, and warning
  state after a popup attempt.
- `expect_current_target_navigation`: consumes and checks the unchanged
  current-document request.
- `_live_attr`: requires the routed node to remain present and returns its
  exact attribute value.
- `setup_post_dispatch_activation_fixture`: builds the mutation matrix.
- `trigger_pointer_and_keyboard_mutation`: drives all six mutations.
- `check_invalidated_default_actions`: checks state, events, target removal,
  request count, request order, and exact URLs.
- `check_live_default_action_control_case`: checks unchanged behavior.

Executable source:
`test/03_system/app/browser/feature/browser_live_default_action_spec.spl`.
