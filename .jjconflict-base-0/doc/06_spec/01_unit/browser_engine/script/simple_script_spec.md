# simple_script_spec

> Purpose: Prove that SimpleScriptExecutor.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_script_spec

Purpose: Prove that SimpleScriptExecutor.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/script/simple_script_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SimpleScriptExecutor.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### SimpleScriptExecutor

#### marks non-empty source execution as dirty and stores the DOM root

- Verify: marks non-empty source execution as dirty and stores the DOM root
   - Expected: exec.dom_dirty() is true
   - Expected: exec.dom_root().tag equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: marks non-empty source execution as dirty and stores the DOM root")
# @req: REQ-BROWSER-ENGINE-SCRIPT-001
var exec = _executor()
val root = BeDomNode.element_with_id(1, "main")
val _ = _install_executor_document(exec, root)
exec.execute("console_log(\"hello\")")
expect(exec.dom_dirty()).to_equal(true)
expect(exec.dom_root().tag).to_equal("main")
```

</details>

#### drains timer and raf callback slots on tick

- Verify: drains timer and raf callback slots on tick
   - Expected: exec.dom_dirty() is true
   - Expected: exec.event_loop().pending_timer_count() equals `0`
   - Expected: exec.event_loop().pending_raf_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: drains timer and raf callback slots on tick")
var event_loop = EventLoop.new()
event_loop.schedule_timer(7, 10, 0)
event_loop.schedule_raf(8, 0, 0)
var exec = SimpleScriptExecutor.new(event_loop, ConsoleBuffer.new())
exec.tick(16000)
expect(exec.dom_dirty()).to_equal(true)
expect(exec.event_loop().pending_timer_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(exec.event_loop().pending_raf_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### retains callback identity and cancels canonical timer work

- Verify: retains callback identity and cancels canonical timer work
   - Expected: exec.register_callback(7, "title \"retained\"") is true
   - Expected: exec.tick(5000).len() equals `0`
   - Expected: timer_callbacks.len() equals `1`
   - Expected: timer_callbacks[0] equals `title "retained"`
   - Expected: frame_callbacks.len() equals `1`
   - Expected: frame_callbacks[0] equals `title "retained"`
   - Expected: exec.callback_count() equals `2`
   - Expected: timeout_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: retains callback identity and cancels canonical timer work")
var exec = _executor()
expect(exec.register_callback(7, "title \"retained\"")).to_equal(true)
val timeout_id = exec.schedule_timeout(7, 0, 10)
val canceled_id = exec.schedule_timeout(7, 0, 20)
exec.schedule_animation_frame(7, 0, 0)
exec.cancel_timer(canceled_id)
expect(exec.tick(5000).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
val timer_callbacks = exec.tick(10000)
expect(timer_callbacks.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(timer_callbacks[0]).to_equal("title \"retained\"")
val frame_callbacks = exec.tick(16000)
expect(frame_callbacks.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(frame_callbacks[0]).to_equal("title \"retained\"")
expect(exec.callback_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(timeout_id).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### resets runner references and document console after retained callback work

- Verify: resets runner references and document console after retained callback work
   - Expected: exec.register_callback(7, "title \"retained\"") is true
   - Expected: exec.has_callback(7) is true
   - Expected: exec._callback_sources[0] equals `title "retained"`
   - Expected: timeout_id equals `1`
   - Expected: callbacks.len() equals `1`
   - Expected: callbacks[0] equals `title "retained"`
   - Expected: exec.callback_count() equals `1`
   - Expected: exec.event_loop().pending_timer_count() equals `0`
   - Expected: exec.event_loop().pending_raf_count() equals `0`
   - Expected: exec.callback_count() equals `0`
   - Expected: exec.has_callback(7) is false
   - Expected: exec._callback_sources.len() equals `0`
   - Expected: exec.console_buffer().entries().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: resets runner references and document console after retained callback work")
var exec = _executor()
val live_dom = BeDomNode.element_with_id(1, "main")
val empty_dom = BeDomNode.element_with_id(1, "#document")
val _ = _install_executor_document(exec, live_dom)
exec.execute("console_log(\"live\")")
expect(exec.register_callback(7, "title \"retained\"")).to_equal(true)
expect(exec.has_callback(7)).to_equal(true)
expect(exec._callback_sources[0]).to_equal("title \"retained\"")
val timeout_id = exec.schedule_timeout(7, 0, 10)
val callbacks = exec.tick(10000)
expect(timeout_id).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(callbacks.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(callbacks[0]).to_equal("title \"retained\"")
expect(exec.callback_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
exec.execute(callbacks[0])
exec.log("log", "document-owned", 0)
expect(exec._runner.dom_root).to_be(live_dom)
expect(exec._runner.event_loop).to_be(exec.event_loop())
expect(exec.console_buffer().entries().len()).to_be_greater_than(0)

val _ = _install_executor_document(exec, empty_dom, 2)

expect(exec.dom_root()).to_be(empty_dom)
expect(exec._runner.dom_root).to_be(empty_dom)
expect(exec._runner.event_loop).to_be(exec.event_loop())
expect(exec.event_loop().pending_timer_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(exec.event_loop().pending_raf_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(exec.callback_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(exec.has_callback(7)).to_equal(false)
expect(exec._callback_sources.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(exec.console_buffer().entries().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(exec._runner.console_buffer).to_be(exec.console_buffer())
```

</details>

#### runs deterministic listener actions during DOM event injection

- Verify: runs deterministic listener actions during DOM event injection
   - Expected: exec.dom_dirty() is true
   - Expected: exec.dom_root().get_attr("data-clicked") equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: runs deterministic listener actions during DOM event injection")
var exec = _executor()
var root = BeDomNode.element_with_id(1, "div")
root.add_event_listener("click", "set-attr:data-clicked=yes")
root.add_event_listener("click", "add-class:clicked")
val index = _install_executor_document(exec, root)
val event = BeDomEvent.create("click", "", true, true)
exec.inject_dom_event_route(
    DomNodeRoute(
        generation: index.generation, node_id: root.node_id
    ),
    event
).unwrap()
expect(exec.dom_dirty()).to_equal(true)
expect(exec.dom_root().get_attr("data-clicked")).to_equal("yes")
expect(exec.dom_root().classes).to_contain("clicked")
```

</details>

#### uses safe fetch fallback without a dispatch

- Verify: uses safe fetch fallback without a dispatch
   - Expected: resp.status equals `0`
   - Expected: resp.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: uses safe fetch fallback without a dispatch")
val exec = _executor()
val resp = exec.fetch(fetch_create_request("https://example.test/data", "GET"))
expect(resp.status).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(resp.ok).to_equal(false)
```

</details>

#### sends fetch requests through installed dispatch

- Verify: sends fetch requests through installed dispatch
   - Expected: resp.status equals `201`
   - Expected: resp.ok is true
   - Expected: resp.headers[0] equals `x-exec`
   - Expected: resp.headers[1] equals `yes`
   - Expected: resp.body equals `created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: sends fetch requests through installed dispatch")
var exec = _executor()
exec.set_fetch_dispatch(ScriptStaticFetchDispatch.create(201, "x-exec: yes", "created"))
val resp = exec.fetch(fetch_create_request("https://example.test/data", "POST"))
expect(resp.status).to_equal(201)  # oracle: 201 — named expected value from the requirement
expect(resp.ok).to_equal(true)
expect(resp.headers[0]).to_equal("x-exec")
expect(resp.headers[1]).to_equal("yes")
expect(resp.body).to_equal("created")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-BROWSER-ENGINE-SCRIPT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60b2d146c5000fc9d0b16b27fa9c414e71eb5b04ca1f1f6808a98881edbda836`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60b2d146c5000fc9d0b16b27fa9c414e71eb5b04ca1f1f6808a98881edbda836`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60b2d146c5000fc9d0b16b27fa9c414e71eb5b04ca1f1f6808a98881edbda836`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/browser_engine/script/simple_script_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/script/simple_script_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/script/simple_script_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/script/simple_script_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/script/simple_script_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/browser_engine/script/simple_script_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/browser_engine/script/simple_script_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks non-empty source execution as dirty and stores the DOM root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/script/simple_script_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drains timer and raf callback slots on tick' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/script/simple_script_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains callback identity and cancels canonical timer work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
