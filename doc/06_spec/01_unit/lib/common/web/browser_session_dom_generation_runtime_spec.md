# Browser Session Dom Generation Runtime Specification

> Tests covering BrowserSession generation-qualified runtime publication.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Dom Generation Runtime Specification

## Scenarios

### BrowserSession generation-qualified runtime publication

#### keeps startup, structural handlers, labels, and nested budgets bounded

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps startup, structural handlers, labels, and nested budgets bounded
- Build the canonical empty document and identity index
- Reuse the current identity index for generation-preserving publish
- Publish set-text as a new generation with valid child identities
   - Expected: buttons.len() equals `1`
   - Expected: be_dom_get_text_content(buttons[0]) equals `changed`
- Rollback a rejected document candidate atomically
- Rollback evaluated runtime and metadata when publication fails
   - Expected: atomic.current_url equals `atomic_url`
   - Expected: atomic.current_title equals `atomic_title`
   - Expected: atomic.current_body_html equals `atomic_body`
   - Expected: atomic.history.len() equals `atomic_history_len`
   - Expected: atomic.session_storage.len() equals `0`
   - Expected: atomic.cookies.count() equals `atomic_cookie_count`
- Rollback a timer runtime when publication fails
   - Expected: atomic.advance_time(1) equals `0`
   - Expected: atomic.current_body_html equals `timer_body`
   - Expected: atomic.advance_time(1) equals `1`
- Forward uncanceled label activation and preserve nested budget
   - Expected: be_dom_get_attr(untouched_inputs[0], "checked") equals ``
   - Expected: be_dom_get_attr(inputs[0], "checked") equals `checked`
- Rollback preactivation after callable budget exhaustion
   - Expected: be_dom_get_attr(budgeted_inputs[0], "checked") equals ``
- Honor cancellation and interactive-descendant suppression
   - Expected: be_dom_get_attr(canceled_inputs[0], "checked") equals ``
   - Expected: be_dom_get_attr(nested_inputs[0], "checked") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 221 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps startup, structural handlers, labels, and nested budgets bounded")
step("Build the canonical empty document and identity index")
var session = BrowserSession.new()
val initial_index = match session.current_dom_identity_index():
    Some(value): value
    nil: fail("Expected a canonical about:blank identity index")
match initial_index.route_for_layout_target_key("path:"):
    Ok(body_route): expect(body_route.node_id).to_be_greater_than(0)
    Err(error): fail("Expected canonical body route: " + error)
match session.runtime_state:
    Some(state):
        expect(state.dom_generation.unwrap().value).to_equal(
            session.document_generation().value
        )
    nil: fail("Expected the about:blank JavaScript mirror")

step("Reuse the current identity index for generation-preserving publish")
var marked_index = initial_index
marked_index.counters.build_visit_count = 777
session.dom_identity_index = Some(marked_index)
session.publish_dom_snapshot(
    session.dom_root(), false, session.runtime_state
).unwrap()
expect(
    session.current_dom_identity_index().unwrap().counters.build_visit_count
).to_equal(777)

step("Publish set-text as a new generation with valid child identities")
session.open_html(
    "https://example.test/generation",
    "<html><body><button id='target' " +
    "onclick='set-text:changed'>change</button></body></html>"
).unwrap()
val before_generation = session.document_generation()
val before_index = session.current_dom_identity_index().unwrap()
val target_route = before_index.route_for_author_id("target").unwrap()
session.dispatch_dom_event_route(
    target_route, "click", true, true
).unwrap()
expect(session.document_generation().value).to_be_greater_than(
    before_generation.value
)
val buttons = be_dom_find_by_tag(session.dom_root(), "button")
expect(buttons.len()).to_equal(1)
expect(be_dom_get_text_content(buttons[0])).to_equal("changed")
expect(buttons[0].children[0].node_id).to_be_greater_than(0)

step("Rollback a rejected document candidate atomically")
val stable_generation = session.document_generation()
val stable_text = be_dom_get_text_content(session.dom_root())
match session.publish_dom_snapshot(BeDomNode.document(), true, nil):
    Ok(_): fail("Invalid node identity must not publish")
    Err(error): expect(error).to_equal("invalid_node_id")
expect(session.document_generation().value).to_equal(
    stable_generation.value
)
expect(be_dom_get_text_content(session.dom_root())).to_equal(
    stable_text
)

step("Rollback evaluated runtime and metadata when publication fails")
var atomic = BrowserSession.new()
atomic.open_html(
    "https://example.test/atomic",
    "<html><body><p>stable</p></body></html>"
).unwrap()
atomic.broker_network_policy = true
expect(atomic.eval_script(
    "document.cookie='kept=1'; 1"
).is_ok()).to_be(true)
val atomic_index = atomic.current_dom_identity_index().unwrap()
val atomic_url = atomic.current_url
val atomic_title = atomic.current_title
val atomic_body = atomic.current_body_html
val atomic_history_len = atomic.history.len()
val atomic_cookie_count = atomic.cookies.count()
val atomic_cookie_header = atomic.cookie_header_for_request(atomic_url)
val atomic_pending_cookie_writes = atomic.pending_script_cookie_writes
atomic.dom_identity_index = nil
match atomic.eval_script(
    "document.title='leak';" +
    "document.body.innerHTML='<p>leak</p>';" +
    "history.pushState({},'', '/leak');" +
    "sessionStorage.setItem('leak','1');" +
    "document.cookie='leak=1'; 1"
):
    Ok(_): fail("Rejected DOM candidate must fail evaluation commit")
    Err(error): expect(error).to_equal("invalid_document")
expect(atomic.current_url).to_equal(atomic_url)
expect(atomic.current_title).to_equal(atomic_title)
expect(atomic.current_body_html).to_equal(atomic_body)
expect(atomic.history.len()).to_equal(atomic_history_len)
expect(atomic.session_storage.len()).to_equal(0)
expect(atomic.cookies.count()).to_equal(atomic_cookie_count)
expect(atomic.cookie_header_for_request(atomic_url)).to_equal(
    atomic_cookie_header
)
expect(atomic.pending_script_cookie_writes).to_equal(
    atomic_pending_cookie_writes
)
atomic.dom_identity_index = Some(atomic_index)
match atomic.eval_script("document.title"):
    Ok(JsValue.String(title)): expect(title).to_equal(atomic_title)
    Ok(_): fail("Expected restored runtime title")
    Err(error): fail("Expected restored runtime: " + error)

step("Rollback a timer runtime when publication fails")
expect(atomic.eval_script(
    "setTimeout(function(){" +
    "document.cookie='timer=leak';" +
    "document.body.innerHTML='<p>timer</p>';},1);"
).is_ok()).to_be(true)
val timer_index = atomic.current_dom_identity_index().unwrap()
val timer_body = atomic.current_body_html
val timer_cookie_header = atomic.cookie_header_for_request(atomic_url)
val timer_pending_cookie_writes = atomic.pending_script_cookie_writes
atomic.dom_identity_index = nil
expect(atomic.advance_time(1)).to_equal(0)
expect(atomic.current_body_html).to_equal(timer_body)
expect(atomic.cookie_header_for_request(atomic_url)).to_equal(
    timer_cookie_header
)
expect(atomic.pending_script_cookie_writes).to_equal(
    timer_pending_cookie_writes
)
atomic.dom_identity_index = Some(timer_index)
expect(atomic.advance_time(1)).to_equal(1)
expect(atomic.current_body_html).to_contain("<p>timer</p>")
expect(atomic.cookie_header_for_request(atomic_url)).to_contain(
    "timer=leak"
)

step("Forward uncanceled label activation and preserve nested budget")
session.open_html(
    "https://example.test/label",
    "<html><body><label id='label' for='choice'>Choice</label>" +
    "<input id='choice' type='checkbox'></body></html>"
).unwrap()
val label_index = session.current_dom_identity_index().unwrap()
val label_route = label_index.route_for_author_id("label").unwrap()
val choice_route = label_index.route_for_author_id("choice").unwrap()
session.dom_dispatch_depth = 1
session.dom_dispatch_budget_remaining = 1
match session.dispatch_dom_event_route(
    choice_route, "click", true, true
):
    Ok(_): fail("Nested dispatch must not reset its shared budget")
    Err(error): expect(error).to_equal(
        "DOM event dispatch budget exceeded"
    )
session.dom_dispatch_depth = 0
session.dom_dispatch_budget_remaining = 0
val untouched_inputs = be_dom_find_by_tag(session.dom_root(), "input")
expect(be_dom_get_attr(untouched_inputs[0], "checked")).to_equal("")
session.active_label_activation_keys["1:999:1000"] = true
session.dispatch_dom_event_route(
    label_route, "click", true, true
).unwrap()
val inputs = be_dom_find_by_tag(session.dom_root(), "input")
expect(be_dom_get_attr(inputs[0], "checked")).to_equal("checked")

step("Rollback preactivation after callable budget exhaustion")
var budgeted = BrowserSession.new()
budgeted.open_html(
    "https://example.test/budgeted",
    "<html><body><input id='choice' type='checkbox'></body></html>"
).unwrap()
budgeted.eval_script(
    "var c=document.getElementById('choice');" +
    "c.addEventListener('click',function(){});" +
    "c.addEventListener('click',function(){});" +
    "c.addEventListener('click',function(){});"
).unwrap()
val budgeted_index = budgeted.current_dom_identity_index().unwrap()
val budgeted_route = budgeted_index.route_for_author_id(
    "choice"
).unwrap()
budgeted.dom_dispatch_depth = 1
budgeted.dom_dispatch_budget_remaining = 9
match budgeted.dispatch_dom_event_route(
    budgeted_route, "click", true, true
):
    Ok(_): fail("Callable listener budget must remain shared")
    Err(error): expect(error).to_equal(
        "DOM event dispatch budget exceeded"
    )
val budgeted_inputs = be_dom_find_by_tag(
    budgeted.dom_root(), "input"
)
expect(be_dom_get_attr(budgeted_inputs[0], "checked")).to_equal("")

step("Honor cancellation and interactive-descendant suppression")
var canceled = BrowserSession.new()
canceled.open_html(
    "https://example.test/label-canceled",
    "<html><body><label id='label' for='choice' " +
    "onclick='prevent-default'>Choice</label>" +
    "<input id='choice' type='checkbox'></body></html>"
).unwrap()
val canceled_index = canceled.current_dom_identity_index().unwrap()
canceled.dispatch_dom_event_route(
    canceled_index.route_for_author_id("label").unwrap(),
    "click", true, true
).unwrap()
val canceled_inputs = be_dom_find_by_tag(canceled.dom_root(), "input")
expect(be_dom_get_attr(canceled_inputs[0], "checked")).to_equal("")

var nested = BrowserSession.new()
nested.open_html(
    "https://example.test/label-interactive",
    "<html><body><label for='choice'><a id='link' href='/next'>" +
    "link</a></label><input id='choice' type='checkbox'></body></html>"
).unwrap()
val nested_index = nested.current_dom_identity_index().unwrap()
nested.dispatch_dom_event_route(
    nested_index.route_for_author_id("link").unwrap(),
    "click", true, true
).unwrap()
val nested_inputs = be_dom_find_by_tag(nested.dom_root(), "input")
expect(be_dom_get_attr(nested_inputs[0], "checked")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_dom_generation_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession generation-qualified runtime publication.
- BrowserSession generation-qualified runtime publication

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `4f7aa3f68c8eb7c74bad7f5e8a44cc24f7f3aadb3de8f82ca5d5108092dbbc1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f7aa3f68c8eb7c74bad7f5e8a44cc24f7f3aadb3de8f82ca5d5108092dbbc1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f7aa3f68c8eb7c74bad7f5e8a44cc24f7f3aadb3de8f82ca5d5108092dbbc1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/web/browser_session_dom_generation_runtime_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_dom_generation_runtime_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_dom_generation_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_dom_generation_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_dom_generation_runtime_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/web/browser_session_dom_generation_runtime_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps startup, structural handlers, labels, and nested budgets bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
