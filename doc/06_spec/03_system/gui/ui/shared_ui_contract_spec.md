# Shared UI semantic contract specification

This host fixture calls the production semantic facade and window-text action
router. It verifies protocol/state conversion, element identity, supported
actions, and structured routing results without reading implementation source.

**Status:** Phase1 seed diagnostics **7/7 PASS**; SPipe docgen UNRUN. Evidence:
`build/phase-one-ui-diagnostic/shared_ui_contract_spec/cycle-one.log`. No native
qualification or measured coverage is claimed. The folded source was synchronized directly.
The `@cover ... 80%` annotations declare admission targets only.

| Source scenarios | Skipped | Pending | Runtime passes |
|---:|---:|---:|---|
| 7 | 0 | 0 | 7, Phase1 seed only |

## Manual scenarios

1. **Map protocol and state.** Create a semantic access fixture, convert it with
   `semantic_ui_snapshot_from_access`, and require protocol 1 in the outer and
   state records, normal mode, the focused canonical ID, title, active surface,
   element count, and mapped element identity.
2. **Map element identity and state.** Pass an access node through
   `SemanticElementInfo.from_access`. Require canonical, surface, widget, kind,
   visible/focused/enabled/selected, text, property, and child identity fields.
3. **Map supported actions.** Convert a form node and require all three actions
   in order: click, type, submit.
4. **Reject a missing target.** Call `win_text_route_action` with an absent
   canonical ID. Require `ok:false`, `target_not_found`, a human-readable
   message, the requested target/action, and no resolved source.
5. **Reject an unsupported action.** Request drag on a form advertising
   click/type/submit. Require `unsupported_operation`, the explanatory message,
   and the source, target, and requested action.
6. **Route supported actions.** Route click, type, and submit individually.
   Require successful results, `ok` codes, explanatory messages, and preserved
   source/target/action identities.
7. **Resolve the default action.** Submit an empty action for the form.
   Require resolution to its first advertised action, click.

Every indexed assertion has an actual length guard. A wrong length records an
expectation failure without continuing into an out-of-bounds access.

These are routing and conversion checks. A successful routing result does not
prove that an adapter consumed the action or mutated its rendered state.
Window-text error codes are typed routing results; these tests do not substitute
them for the HTTP error/message schema in the broader protocol contract.

## Scope and traceability

Authoritative architecture: [Shared UI contract](../../../../04_architecture/ui/shared_ui_contract.md).

| Requirement | Executable | Coverage |
|---|---|---|
| REQ-SSPEC-SYSTEM | `test/03_system/gui/ui/shared_ui_contract_spec.spl` | Protocol/state, identity, advertised actions, real success/error routing |

Production owners are `src/lib/common/ui/semantic_contract.spl` and
`src/lib/common/ui/win_text_access.spl`.

The superseded legacy `test/system/ui/shared_ui_contract_spec.spl` contained
literal-only versions of the four contract topics and an additional literal-only
Simple Lab surface declaration. The four topics are covered behaviorally here.
The Simple Lab declaration's intended obligation is retained explicitly:
`app.simple_lab` must satisfy the S4 HTTP/WebSocket shared protocol; its actual
loopback evidence belongs to
`test/03_system/tools/simple_lab/lab_shared_ui_contract_spec.spl`.
That spec was not run by this repair, so Simple Lab S4 is unverified.

Live Web and TUI-Web endpoint parity, HTTP error bodies, action consumption,
read-after-write state, and each other staged surface remain broader acceptance
work under the architecture. This fixture does not close those obligations,
and it does not replace them with optional skips or a Rust-seed run.

<details>
<summary>Executable SSpec, including reusable setup</summary>

```simple
# Purpose and audience: shared semantic UI identity and action contracts for UI maintainers.
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/lib/common/ui/semantic_contract.spl 80%
# @cover src/lib/common/ui/win_text_access.spl 80%
# Coverage percentages are admission targets, not measured coverage.
# architecture: doc/04_architecture/ui/shared_ui_contract.md
# research: doc/01_research/domain/sspec_documentization_maintenance.md ; plan: doc/03_plan/sspec_modernization_plan.md ; design: doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md
# @tag:system
# Host-fixture evidence, not live cross-surface protocol verification.
# Simple Lab's S4 HTTP/WebSocket obligation remains at:
# test/03_system/tools/simple_lab/lab_shared_ui_contract_spec.spl

use std.spec.{describe, it, expect}
use std.spec.step
use common.ui.access_types.{UI_ACCESS_PROTOCOL_VERSION, UiAccessNode, UiAccessProp, UiAccessSurface}
use common.ui.semantic_contract.{SemanticElementInfo, semantic_ui_snapshot_from_access}
use common.ui.win_text_access.{WinTextSnapshot, WinTextActionRequest, win_text_snapshot_from_parts, win_text_route_action}

# @inline
fn shared_contract_form() -> UiAccessNode:
    UiAccessNode(
        canonical_id: "main#form",
        surface_id: "main",
        widget_id: "form",
        kind: "form",
        visible: true,
        focused: true,
        enabled: true,
        selected: true,
        text_value: "Submit changes",
        props: [UiAccessProp(key: "source", value: "simple_ui")],
        child_ids: ["main#field"],
        action_names: ["click", "type", "submit"]
    )

# @inline
fn shared_contract_snapshot() -> WinTextSnapshot:
    val form = shared_contract_form()
    val surface = UiAccessSurface(
        surface_id: "main",
        title: "Shared contract fixture",
        active: true,
        window_id: "window-1",
        app_id: "contract-fixture",
        root_canonical_id: "main#form"
    )
    win_text_snapshot_from_parts("NORMAL", "main", [surface], [form], [])

# @inline
fn shared_contract_request(target_id: text, action: text) -> WinTextActionRequest:
    WinTextActionRequest(target_id: target_id, action: action, text_value: "", x: 0, y: 0)

describe "Shared UI semantic contract":
    # @manual scenario evidence
    it "should preserve protocol and focused state through snapshot conversion":
        step("Create the shared semantic UI fixture")
        val fixture = shared_contract_snapshot()
        step("Map the access snapshot to the semantic contract")
        val snapshot = semantic_ui_snapshot_from_access(fixture.access, "S1", "available")
        expect(UI_ACCESS_PROTOCOL_VERSION).to_equal(1)
        expect(snapshot.protocol_version).to_equal(1)
        expect(snapshot.state.protocol_version).to_equal(1)
        expect(snapshot.state.mode).to_equal("NORMAL")
        expect(snapshot.state.focused_id).to_equal("main#form")
        expect(snapshot.state.title).to_equal("Shared contract fixture")
        expect(snapshot.state.active_surface).to_equal("main")
        expect(snapshot.state.element_count).to_equal(1)
        expect(snapshot.elements.len()).to_equal(1)
        if snapshot.elements.len() == 1:
            expect(snapshot.elements[0].canonical_id).to_equal("main#form")

    it "should preserve every semantic element identity and state field":
        step("Create the shared semantic UI fixture")
        val node = shared_contract_form()
        step("Map the access node to a semantic element")
        val element = SemanticElementInfo.from_access(node)
        expect(element.canonical_id).to_equal("main#form")
        expect(element.surface_id).to_equal("main")
        expect(element.widget_id).to_equal("form")
        expect(element.kind).to_equal("form")
        expect(element.visible).to_equal(true)
        expect(element.focused).to_equal(true)
        expect(element.enabled).to_equal(true)
        expect(element.selected).to_equal(true)
        expect(element.text).to_equal("Submit changes")
        expect(element.props.len()).to_equal(1)
        if element.props.len() == 1:
            expect(element.props[0].key).to_equal("source")
            expect(element.props[0].value).to_equal("simple_ui")
        expect(element.child_ids.len()).to_equal(1)
        if element.child_ids.len() == 1:
            expect(element.child_ids[0]).to_equal("main#field")

    it "should preserve all supported actions in declaration order":
        step("Create the shared semantic UI fixture")
        val node = shared_contract_form()
        step("Map supported actions through the semantic element facade")
        val element = SemanticElementInfo.from_access(node)
        expect(element.action_names.len()).to_equal(3)
        if element.action_names.len() == 3:
            expect(element.action_names[0]).to_equal("click")
            expect(element.action_names[1]).to_equal("type")
            expect(element.action_names[2]).to_equal("submit")

    it "should return a structured failure for a missing target":
        step("Create the shared semantic UI fixture")
        val fixture = shared_contract_snapshot()
        step("Route an action to a missing canonical identity")
        val result = win_text_route_action(fixture, shared_contract_request("main#absent", "click"))
        expect(result.ok).to_equal(false)
        expect(result.code).to_equal("target_not_found")
        expect(result.message).to_equal("target not found")
        expect(result.source_id).to_equal("")
        expect(result.target_id).to_equal("main#absent")
        expect(result.action).to_equal("click")

    it "should return a structured failure for an unsupported action":
        step("Create the shared semantic UI fixture")
        val fixture = shared_contract_snapshot()
        step("Route an action absent from the target's supported actions")
        val result = win_text_route_action(fixture, shared_contract_request("main#form", "drag"))
        expect(result.ok).to_equal(false)
        expect(result.code).to_equal("unsupported_operation")
        expect(result.message).to_equal("unsupported action 'drag' for form")
        expect(result.source_id).to_equal("simple_ui")
        expect(result.target_id).to_equal("main#form")
        expect(result.action).to_equal("drag")

    it "should route each advertised action with its target and source identity":
        step("Create the shared semantic UI fixture")
        val fixture = shared_contract_snapshot()
        step("Route supported click type and submit actions")
        for action in ["click", "type", "submit"]:
            val result = win_text_route_action(fixture, shared_contract_request("main#form", action))
            expect(result.ok).to_equal(true)
            expect(result.code).to_equal("ok")
            expect(result.message).to_equal("routed action '" + action + "'")
            expect(result.source_id).to_equal("simple_ui")
            expect(result.target_id).to_equal("main#form")
            expect(result.action).to_equal(action)

    it "should resolve an omitted action to the first advertised action":
        step("Create the shared semantic UI fixture")
        val fixture = shared_contract_snapshot()
        step("Route the target's default action")
        val result = win_text_route_action(fixture, shared_contract_request("main#form", ""))
        expect(result.ok).to_equal(true)
        expect(result.code).to_equal("ok")
        expect(result.action).to_equal("click")
        expect(result.source_id).to_equal("simple_ui")
        expect(result.target_id).to_equal("main#form")
```

</details>
