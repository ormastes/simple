# Generation-qualified DOM identity index

> The document identity owner builds stable typed routes, resolves DOM

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generation-qualified DOM identity index

The document identity owner builds stable typed routes, resolves DOM

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/dom_identity_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The document identity owner builds stable typed routes, resolves DOM
associations without recursive lookup, and rejects routes captured from a
replaced document generation.

## Scenarios

### Generation-qualified DOM identity index

#### keeps routes stable only for the committed document generation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps routes stable only for the committed document generation
- Build the document identity index
- Dispatch through stable routes
- Replace the document during a handler
- Reject stale routes and release the index


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("keeps routes stable only for the committed document generation")
step("Build the document identity index")
val fixture = setup_dom_identity_generation_fixture()
check_dom_identity_index_built(fixture)

step("Dispatch through stable routes")
check_stable_route_dispatch(fixture)

step("Replace the document during a handler")
val replacement = check_document_replacement_during_handler(
    fixture.deep_route
)

step("Reject stale routes and release the index")
check_stale_routes_and_index_release(
    fixture.index, fixture.deep_route, replacement
)
```

</details>

#### admits only canonical positive generation values

- admits only canonical positive generation values
   - Expected: _generation(5).value equals `5`
   - Expected: advanced.value equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("admits only canonical positive generation values")
expect(DomDocumentGeneration.create(0)).to_equal(
    Err("invalid_generation")
)
expect(DomDocumentGeneration.create(-1)).to_equal(
    Err("invalid_generation")
)
expect(_generation(5).value).to_equal(5)
val advanced = match _generation(5).next():
    Ok(value): value
    Err(reason): fail("Expected successor generation: {reason}")
expect(advanced.value).to_equal(6)
expect(DomDocumentGeneration(
    value: 9223372036854775807
).next()).to_equal(Err("generation_exhausted"))

# `create` is not the only way in: a generation built directly around a
# non-positive value must still be refused by the builder itself,
# before any node is visited.
val root = html_tree_builder_build("<p id='a'>x</p>")
expect(dom_identity_index_build(
    root, DomDocumentGeneration(value: 0)
)).to_equal(Err("invalid_generation"))
expect(dom_identity_index_build(
    root, DomDocumentGeneration(value: -3)
)).to_equal(Err("invalid_generation"))
```

</details>

#### round-trips route text and rejects every non-canonical form

- round-trips route text and rejects every non-canonical form
   - Expected: dom_node_route_text(route) equals `dom-route-v1:1:7`
   - Expected: dom_node_route_parse("dom-route-v1:1:7") equals `Ok(route)`
   - Expected: dom_node_route_parse("nope") equals `Err("invalid_route")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("round-trips route text and rejects every non-canonical form")
val route = DomNodeRoute(generation: _generation(1), node_id: 7)
expect(dom_node_route_text(route)).to_equal("dom-route-v1:1:7")
expect(dom_node_route_parse("dom-route-v1:1:7")).to_equal(Ok(route))
expect(dom_node_route_parse("nope")).to_equal(Err("invalid_route"))
expect(dom_node_route_parse("dom-route-v2:1:7")).to_equal(
    Err("invalid_route")
)
expect(dom_node_route_parse("dom-route-v1:1:7:1")).to_equal(
    Err("invalid_route")
)
expect(dom_node_route_parse("dom-route-v1:0:1")).to_equal(
    Err("invalid_route")
)
expect(dom_node_route_parse("dom-route-v1:01:1")).to_equal(
    Err("invalid_route")
)
expect(dom_node_route_parse("dom-route-v1:1:-1")).to_equal(
    Err("invalid_route")
)
expect(dom_node_route_parse("dom-route-v1:1:")).to_equal(
    Err("invalid_route")
)
```

</details>

#### separates malformed layout targets from targets that are absent

- separates malformed layout targets from targets that are absent
   - Expected: index.author_id_for_route(first_div) equals `Some("a")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("separates malformed layout targets from targets that are absent")
val index = _index(
    "<body><div id='a'><input id='i' type='hidden'></div>" +
    "<form id='f'><input id='r' type='radio' name='n'></form>" +
    "</body>",
    1
)
expect(index.route_for_layout_target_key("id:")).to_equal(
    Err("invalid_target")
)
expect(index.route_for_layout_target_key("q:1")).to_equal(
    Err("invalid_target")
)
expect(index.route_for_layout_target_key("path:-1")).to_equal(
    Err("invalid_target")
)
expect(index.route_for_layout_target_key("id:zzz")).to_equal(
    Err("target_not_found")
)
expect(index.route_for_layout_target_key("path:99")).to_equal(
    Err("target_not_found")
)
val first_div = _route(index, "a")
expect(index.route_for_layout_target_key("path:0")).to_equal(
    Ok(first_div)
)
expect(index.layout_target_key_for_route(first_div)).to_equal(
    Some("path:0")
)
expect(index.author_id_for_route(first_div)).to_equal(Some("a"))
expect(index.route_for_author_id("")).to_be_nil()
expect(index.route_for_author_id("zzz")).to_be_nil()
```

</details>

#### refuses every association lookup made with a foreign generation

- refuses every association lookup made with a foreign generation
   - Expected: index.event_path_for_route(foreign).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("refuses every association lookup made with a foreign generation")
val index = _index(
    "<body><div id='a'><input id='i' type='hidden'></div>" +
    "<form id='f'><input id='r' type='radio' name='n'></form>" +
    "</body>",
    1
)
val live = _route(index, "r")
expect(index.contains_route(live)).to_be(true)
expect(index.form_owner_for_route(live)).to_equal(
    Some(_route(index, "f"))
)
val foreign = DomNodeRoute(
    generation: _generation(2), node_id: live.node_id
)
expect(index.contains_route(foreign)).to_be(false)
expect(index.form_owner_for_route(foreign)).to_be_nil()
expect(index.control_for_label_route(foreign)).to_be_nil()
expect(index.radio_group_for_route(foreign)).to_be_nil()
expect(index.author_id_for_route(foreign)).to_be_nil()
expect(index.path_for_route(foreign)).to_be_nil()
expect(index.event_path_for_route(foreign).len()).to_equal(0)
```

</details>

#### counts exactly one visit per node in each of the two build passes

- counts exactly one visit per node in each of the two build passes
   - Expected: index.counters.pass_count equals `2`
   - Expected: index.counters.node_count equals `8`
   - Expected: index.counters.build_visit_count equals `16`
   - Expected: index.counters.duplicate_author_id_count equals `0`
   - Expected: index.counters.resolved_association_count equals `1`
   - Expected: index.counters.unresolved_association_count equals `0`
   - Expected: index.counters.layout_relation_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("counts exactly one visit per node in each of the two build passes")
val index = _index(
    "<body><div id='a'><input id='i' type='hidden'></div>" +
    "<form id='f'><input id='r' type='radio' name='n'></form>" +
    "</body>",
    1
)
expect(index.counters.pass_count).to_equal(2)
expect(index.counters.node_count).to_equal(8)
expect(index.counters.build_visit_count).to_equal(16)
expect(index.counters.duplicate_author_id_count).to_equal(0)
expect(index.counters.resolved_association_count).to_equal(1)
expect(index.counters.unresolved_association_count).to_equal(0)
expect(index.counters.layout_relation_count).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `a94d16995ded1570f91aeeb5265a250af1867eff2a479e6bf8fe72fe9af154dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a94d16995ded1570f91aeeb5265a250af1867eff2a479e6bf8fe72fe9af154dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a94d16995ded1570f91aeeb5265a250af1867eff2a479e6bf8fe72fe9af154dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/dom_identity_index_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/dom_identity_index_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/dom_identity_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/dom_identity_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/dom_identity_index_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/dom_identity_index_spec.spl:315:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps routes stable only for the committed document generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/dom_identity_index_spec.spl:336:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only canonical positive generation values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/dom_identity_index_spec.spl:366:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips route text and rejects every non-canonical form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
