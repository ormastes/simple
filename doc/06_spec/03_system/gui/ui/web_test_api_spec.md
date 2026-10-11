# Web UI Test API handler specification

The production `dispatch_test_api` mount routes requests through
`app.ui.test_api.handler` using a real three-widget `UISession`.
The event recorder observes injected actions and keys; unexpected event kinds
fail explicitly.

**Evidence class:** host fixture. This specification exercises routing, session
serialization, canonical access snapshots, and event injection. It does not prove
TCP transport, browser rendering, or application consumption of injected events.

**Runtime status:** Phase1 seed diagnostic **7/7 PASS**, after repairing the
JSON member lookup exposed by the first run (6/7). The unchanged valid key-event
payload now injects the requested event. Retained evidence:
`build/phase-one-ui-diagnostic/web_test_api_spec/cycle-two.log` and
`build/phase-one-ui-diagnostic/json-repair-inputs.json`.
This dedicated bootstrap diagnostic does not establish self-hosted/native
product qualification. SPipe docgen remains unrun; this manual was synchronized
directly with the executable source.

| Source scenarios | Skipped | Pending | Runtime passes |
|---:|---:|---:|---|
| 7 | 0 | 0 | 7, Phase1 seed only |

## Manual scenarios

1. **Query readiness and session state.** Create the web UI test fixture, then
   query readiness and state. Require JSON responses, protocol version 1,
   normal mode, the fixture title, exactly three elements, and no injected events.
2. **Query fixture elements and the canonical access snapshot.** Create the
   fixture and query all elements, the action button, and the canonical snapshot.
   Require root/input/button identities, button kind, label and action, and
   canonical `main#...` identities. Reads must inject no events.
3. **Dispatch a click.** Create the fixture and post a click for `action_btn`.
   Require HTTP 200 with `ok:true` and exactly `Action("click_action_btn")`.
4. **Dispatch typed text.** Create the fixture and type `Hi` into
   `web_api_input`. Require the focus action followed by `KeyPress("H")`
   and `KeyPress("i")`, in that order, with no additional events.
5. **Dispatch a named key.** Post the key event `Enter`. Require HTTP 200,
   `ok:true`, and exactly one `KeyPress("Enter")`.
6. **Reject malformed actions.** Omit the click/type target or the key value.
   Require HTTP 400 and the corresponding missing-field response; inject no events.
7. **Reject invalid queries and routing.** Omit an element ID, request an absent
   element or route, and use DELETE on readiness. Require the respective
   400/404/404/405 responses and error kinds; inject no events.

Each scenario creates its own fixture and resets the event recorder. Shared
setup is folded below; the actual production handlers generate every observed
response and event.

## Traceability

| Requirement | Executable | Manual | Coverage |
|---|---|---|---|
| REQ-SSPEC-SYSTEM | `test/03_system/gui/ui/web_test_api_spec.spl` | `doc/06_spec/03_system/gui/ui/web_test_api_spec.md` | Ready/state, element reads, canonical snapshot, click/type/key injection, rejection contracts |

Production owners: `src/app/ui.test_api/handler.spl` and
`src/app/ui.test_api/mount.spl`. Their `@cover` percentages are admission
targets, not measured coverage. The identical legacy spec under
`test/system/ui/` was removed; all three former placeholder topics are
subsumed by these behavioral scenarios.

<details>
<summary>Executable SSpec, including fixture and event recorder</summary>

```simple
# Purpose and audience: Web UI API handler behavior for UI maintainers.
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/app/ui.test_api/handler.spl 80%
# @cover src/app/ui.test_api/mount.spl 80%
# Coverage percentages are admission targets, not measured coverage.
# research: doc/01_research/domain/sspec_documentization_maintenance.md ; plan: doc/03_plan/sspec_modernization_plan.md ; architecture: doc/04_architecture/sspec_documentization_maintenance.md ; design: doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md
# @tag:system
# Host-fixture evidence: real production handlers and session, without TCP or browser rendering.

use std.spec.*
use std.spec.step
use common.ui.builder.{column, button, text_input, build_tree_with_title}
use common.ui.widget.{UIEvent}
use nogc_sync_mut.ui.session.{UISession}
use app.ui.test_api.mount.{dispatch_test_api}

var web_api_events: [text] = []

# @inline
fn create_web_api_fixture() -> UISession:
    web_api_events = []
    val root = column("web_api_root", [
        button("action_btn", "Run action", "run_action"),
        text_input("web_api_input", "Enter text")
    ])
    val tree = build_tree_with_title(root, "Web API fixture", "default")
    return UISession.new(tree)

# The recorder observes the production handler's actual callback output.
# Unexpected event kinds fail rather than disappearing from the oracle.
fn record_web_api_event(event: UIEvent):
    match event:
        UIEvent.Action(name):
            web_api_events.push("action:" + name)
        UIEvent.KeyPress(key):
            web_api_events.push("key:" + key)
        _:
            assert(false)

describe "Web UI Test API handler integration":
    # @manual scenario evidence
    it "should query readiness and session state":
        step("Create the web UI test fixture")
        val session = create_web_api_fixture()
        step("Query readiness and elements")
        val ready = dispatch_test_api("/api/test/ready", "GET", "", session, record_web_api_event)
        expect(ready.0).to_equal(200)
        expect(ready.1).to_equal("application/json")
        expect(ready.2).to_equal("{\"ready\":true,\"protocol_version\":1}")
        val state = dispatch_test_api("/api/test/state", "GET", "", session, record_web_api_event)
        expect(state.0).to_equal(200)
        expect(state.1).to_equal("application/json")
        expect(state.2).to_contain("\"mode\":\"NORMAL\"")
        expect(state.2).to_contain("\"title\":\"Web API fixture\"")
        expect(state.2).to_contain("\"element_count\":3,")
        expect(web_api_events.len()).to_equal(0)

    it "should query fixture elements and the canonical access snapshot":
        step("Create the web UI test fixture")
        val session = create_web_api_fixture()
        step("Query readiness and elements")
        val elements = dispatch_test_api("/api/test/elements", "GET", "", session, record_web_api_event)
        expect(elements.0).to_equal(200)
        expect(elements.1).to_equal("application/json")
        expect(elements.2).to_start_with("[")
        expect(elements.2).to_end_with("]")
        expect(elements.2).to_contain("\"id\":\"web_api_root\"")
        expect(elements.2).to_contain("\"id\":\"action_btn\",\"kind\":\"button\"")
        expect(elements.2).to_contain("\"id\":\"web_api_input\"")
        val element = dispatch_test_api("/api/test/element?id=action_btn", "GET", "", session, record_web_api_event)
        expect(element.0).to_equal(200)
        expect(element.2).to_contain("\"id\":\"action_btn\",\"kind\":\"button\"")
        expect(element.2).to_contain("\"label\":\"Run action\"")
        expect(element.2).to_contain("\"action\":\"run_action\"")
        val snapshot = dispatch_test_api("/api/test/ui/snapshot", "GET", "", session, record_web_api_event)
        expect(snapshot.0).to_equal(200)
        expect(snapshot.2).to_contain("main#action_btn")
        expect(snapshot.2).to_contain("main#web_api_input")
        expect(web_api_events.len()).to_equal(0)

    it "should dispatch a click to the requested widget":
        step("Create the web UI test fixture")
        val session = create_web_api_fixture()
        step("Dispatch supported actions")
        val response = dispatch_test_api("/api/test/click", "POST", "{\"id\":\"action_btn\"}", session, record_web_api_event)
        expect(response.0).to_equal(200)
        expect(response.1).to_equal("application/json")
        expect(response.2).to_equal("{\"ok\":true}")
        expect(web_api_events.len()).to_equal(1)
        expect(web_api_events[0]).to_equal("action:click_action_btn")

    it "should focus the input before injecting typed characters in order":
        step("Create the web UI test fixture")
        val session = create_web_api_fixture()
        step("Dispatch supported actions")
        val response = dispatch_test_api("/api/test/type", "POST", "{\"id\":\"web_api_input\",\"text\":\"Hi\"}", session, record_web_api_event)
        expect(response.0).to_equal(200)
        expect(response.2).to_equal("{\"ok\":true}")
        expect(web_api_events.len()).to_equal(3)
        expect(web_api_events[0]).to_equal("action:focus_web_api_input")
        expect(web_api_events[1]).to_equal("key:H")
        expect(web_api_events[2]).to_equal("key:i")

    it "should dispatch a named key through the event endpoint":
        step("Create the web UI test fixture")
        val session = create_web_api_fixture()
        step("Dispatch supported actions")
        val response = dispatch_test_api("/api/test/event", "POST", "{\"event_type\":\"key\",\"key\":\"Enter\"}", session, record_web_api_event)
        expect(response.0).to_equal(200)
        expect(response.2).to_equal("{\"ok\":true}")
        expect(web_api_events.len()).to_equal(1)
        if web_api_events.len() == 1:
            expect(web_api_events[0]).to_equal("key:Enter")

    it "should reject missing action fields without injecting events":
        step("Create the web UI test fixture")
        val session = create_web_api_fixture()
        step("Reject malformed action requests")
        val click = dispatch_test_api("/api/test/click", "POST", "{}", session, record_web_api_event)
        expect(click.0).to_equal(400)
        expect(click.2).to_contain("\"error\":\"missing_field\"")
        val typed = dispatch_test_api("/api/test/type", "POST", "{\"text\":\"Hi\"}", session, record_web_api_event)
        expect(typed.0).to_equal(400)
        expect(typed.2).to_contain("Missing required field: id")
        val key = dispatch_test_api("/api/test/event", "POST", "{\"event_type\":\"key\"}", session, record_web_api_event)
        expect(key.0).to_equal(400)
        expect(key.2).to_contain("Missing required field: key")
        expect(web_api_events.len()).to_equal(0)

    it "should reject missing elements unknown routes and unsupported methods":
        step("Create the web UI test fixture")
        val session = create_web_api_fixture()
        step("Query invalid elements and routes")
        val missing_id = dispatch_test_api("/api/test/element", "GET", "", session, record_web_api_event)
        expect(missing_id.0).to_equal(400)
        expect(missing_id.2).to_contain("Missing required field: id")
        val missing_element = dispatch_test_api("/api/test/element?id=absent", "GET", "", session, record_web_api_event)
        expect(missing_element.0).to_equal(404)
        expect(missing_element.2).to_contain("\"error\":\"element_not_found\"")
        val route = dispatch_test_api("/api/test/absent", "GET", "", session, record_web_api_event)
        expect(route.0).to_equal(404)
        expect(route.2).to_contain("\"error\":\"not_found\"")
        val method = dispatch_test_api("/api/test/ready", "DELETE", "", session, record_web_api_event)
        expect(method.0).to_equal(405)
        expect(method.2).to_contain("\"error\":\"method_not_allowed\"")
        expect(web_api_events.len()).to_equal(0)
```

</details>
