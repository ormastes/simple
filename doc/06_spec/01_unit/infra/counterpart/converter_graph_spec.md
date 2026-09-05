# Counterpart Converter Graph

> A counterpart comparison almost never compares two artifacts in the same shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Converter Graph

A counterpart comparison almost never compares two artifacts in the same shape.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/converter_graph_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A counterpart comparison almost never compares two artifacts in the same shape.
Chrome emits a DOM snapshot; the Simple resolver emits a canonical node arena;
a GPU lane emits a device record. Something must carry each of them to a shared
canonical schema, and that something is a *named, versioned converter* — never
an unnamed normalization buried in the comparator.

The audience is an engineer authoring a counterpart scenario. You register the
converter edges you are willing to stand behind, and you ask the graph for a
route. The graph either hands you a typed route — its ordered edge list, the
route hash that lands in the provenance receipt, and one conversion receipt per
edge — or it refuses and tells you which rule it refused under.

## Scope and Preconditions

Schema identifiers are pinned as `<name>@<version>` with a version of at least
one. A converter that does not pin both of its schemas cannot be registered.
Routes are simple paths, bounded at eight edges.

## Primary Workflow

Register edges, then resolve. A route's loss is the worst loss among its edges.
Between two candidate routes the graph prefers lower loss, then fewer edges;
anything still tied is ambiguous and is refused rather than guessed.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Conversion loss | identity < representation_only < canonicalizing < semantic_projection < diagnostic_only |
| Route hash | Deterministic identity of the chosen edge chain, recorded in provenance |
| Fail-closed routing | Nine named refusals, listed in design §6.3 |

## Related Specifications

- [Relation and matrix engine](relation_matrix_spec.spl) — what consumes a route

## Evidence and Provenance

Every scenario below is executable against
`src/lib/nogc_sync_mut/spec/evidence/counterpart/converter_graph.spl`. The
refusal scenarios are the load-bearing ones: each is written so that removing
the corresponding guard turns it red.

## Recovery and Troubleshooting

A refusal carries a `rejection_code` and a human-readable `rejection_detail`.
Fix the graph or the plan; do not widen the relation to make the refusal go
away.

## Compatibility and Limitations

Route search is bounded at `COUNTERPART_ROUTE_MAX_DEPTH` edges. Deeper chains
resolve as `no_route` rather than searching indefinitely.

## Scenarios

### Counterpart converter registry

#### pins a schema version and refuses an unpinned one

- pins a schema version and refuses an unpinned one
- Read the version off a pinned schema id
- Refuse a schema id with no version, a bad version, or padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("pins a schema version and refuses an unpinned one")
step("Read the version off a pinned schema id")
assert_equal(schema_version_of(CHROME), 1)
step("Refuse a schema id with no version, a bad version, or padding")
assert_equal(schema_version_of("chrome.dom_snapshot"), 0 - 1)
assert_equal(schema_version_of("chrome.dom_snapshot@0"), 0 - 1)
assert_equal(schema_version_of("chrome.dom_snapshot@01"), 0 - 1)
assert_false(schema_id_is_valid("@1"))
```

</details>

#### accepts a well-formed edge and indexes it by its source schema

- accepts a well-formed edge and indexes it by its source schema
- Register a two-edge chain
- Confirm the registry is clean and the edge is indexed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts a well-formed edge and indexes it by its source schema")
step("Register a two-edge chain")
val registry = a_registry_with_a_clean_two_edge_chain()
step("Confirm the registry is clean and the edge is indexed")
assert_true(registry_is_clean(registry))
assert_equal(registry_edge_count(registry), 2)
assert_equal(registry_edges_from(registry, CHROME).len(), 1)
```

</details>

#### refuses a second registration of an already-known converter id

- refuses a second registration of an already-known converter id
- Register one converter, then register its id again
- Confirm the duplicate was rejected and never entered the graph


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a second registration of an already-known converter id")
step("Register one converter, then register its id again")
var registry = converter_registry()
registry = registry_register(registry, converter_manifest(
    "dup_id", "1.0.0", CHROME, CHROME_IR, ConversionLoss.identity))
registry = registry_register(registry, converter_manifest(
    "dup_id", "2.0.0", CHROME_IR, CANON, ConversionLoss.identity))
step("Confirm the duplicate was rejected and never entered the graph")
assert_false(registry_is_clean(registry))
assert_equal(registry_edge_count(registry), 1)
assert_true(registry.rejections[0].contains("duplicate converter registration"))
```

</details>

#### refuses a converter that derives its expected value from the candidate

- refuses a converter that derives its expected value from the candidate
- Declare a converter that states it reads the candidate's own output
- Confirm the manifest is refused, and that the reason echoes the source
- Confirm it never enters the graph
- Confirm a rename cannot walk around the gate
- Confirm an honest upstream source is still permitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a converter that derives its expected value from the candidate")
step("Declare a converter that states it reads the candidate's own output")
val manifest = converter_manifest_full(
    "peek_candidate", "1.0.0", CHROME, CANON,
    ConversionLoss.canonicalizing, true, [], [],
    ["derives_expected_from:candidate_output"])
step("Confirm the manifest is refused, and that the reason echoes the source")
val reasons = converter_manifest_rejections(manifest)
assert_equal(reasons.len(), 1)
assert_true(reasons[0].contains("candidate_output"))
step("Confirm it never enters the graph")
var registry = converter_registry()
registry = registry_register(registry, manifest)
assert_equal(registry_edge_count(registry), 0)
step("Confirm a rename cannot walk around the gate")
assert_true(manifest_derives_expected_from_candidate(converter_manifest_full(
    "renamed", "1.0.0", CHROME, CANON, ConversionLoss.identity, true, [], [],
    ["derives_expected_from:candidate_under_test.stdout"])))
step("Confirm an honest upstream source is still permitted")
assert_false(manifest_derives_expected_from_candidate(converter_manifest_full(
    "honest", "1.0.0", CHROME, CANON, ConversionLoss.identity, true, [], [],
    ["derives_expected_from:normative_vector_file"])))
```

</details>

#### refuses to route across an edge that derives from the candidate

- refuses to route across an edge that derives from the candidate
- Force such an edge past the registry into a graph directly
- Confirm the graph refuses the route in its own right


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses to route across an edge that derives from the candidate")
step("Force such an edge past the registry into a graph directly")
val poisoned = ConverterRegistry(
    converters: [converter_manifest_full(
        "peek_candidate", "1.0.0", CHROME, CANON,
        ConversionLoss.canonicalizing, true, [], [],
        ["derives_expected_from:candidate_output"])],
    rejections: []
)
step("Confirm the graph refuses the route in its own right")
val resolution = resolve_route(poisoned, route_request(
    CHROME, CANON, CounterpartRelation.semantic_equal, 12, "in-hash"))
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "derived_expected_value")
```

</details>

#### refuses an edge whose schema carries no version

- refuses an edge whose schema carries no version
- Register an edge with an unpinned target schema
- Confirm the edge was refused


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses an edge whose schema carries no version")
step("Register an edge with an unpinned target schema")
var registry = converter_registry()
registry = registry_register(registry, converter_manifest(
    "unpinned", "1.0.0", CHROME, "canonical.node_arena", ConversionLoss.identity))
step("Confirm the edge was refused")
assert_equal(registry_edge_count(registry), 0)
assert_true(registry.rejections[0].contains("missing/invalid to_schema"))
```

</details>

### Counterpart converter graph routing

#### resolves a multi-edge route and reports its worst-case loss

- resolves a multi-edge route and reports its worst-case loss
- Ask for a canonical-exact route across the two-edge chain
- Confirm a typed route came back, not a bare verdict
- Confirm route loss is the MAX of its edges, not the first or the last
- Confirm the route carries a hash and one receipt per edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("resolves a multi-edge route and reports its worst-case loss")
step("Ask for a canonical-exact route across the two-edge chain")
val registry = a_registry_with_a_clean_two_edge_chain()
val resolution = resolve_route(registry, route_request(
    CHROME, CANON, CounterpartRelation.canonical_exact, 42, "in-hash"))
step("Confirm a typed route came back, not a bare verdict")
assert_true(resolution.resolved)
assert_equal(resolution.route.edges.len(), 2)
assert_equal(route_edge_ids(resolution.route)[0], "chrome_json_to_ir")
step("Confirm route loss is the MAX of its edges, not the first or the last")
assert_equal(resolution.route.loss_rank, 2)
step("Confirm the route carries a hash and one receipt per edge")
assert_true(resolution.route.route_hash.starts_with("croute/v1"))
assert_equal(resolution.route.receipts.len(), 2)
assert_equal(resolution.route.receipts[0].input_hash, "in-hash")
assert_equal(resolution.route.receipts[1].input_hash,
    resolution.route.receipts[0].output_hash)
```

</details>

#### resolves an identity route when source and target already agree

- resolves an identity route when source and target already agree
- Ask for a route from a schema to itself
- Confirm it resolves with no edges and no loss


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("resolves an identity route when source and target already agree")
step("Ask for a route from a schema to itself")
val registry = a_registry_with_a_clean_two_edge_chain()
val resolution = resolve_route(registry, route_request(
    CANON, CANON, CounterpartRelation.byte_exact, 7, "in-hash"))
step("Confirm it resolves with no edges and no loss")
assert_true(resolution.resolved)
assert_equal(resolution.route.edges.len(), 0)
assert_equal(resolution.route.loss_rank, 0)
```

</details>

### Counterpart converter graph refuses unsound routes

#### refuses an exact relation whose only route is a semantic projection

- refuses an exact relation whose only route is a semantic projection
- Register a single semantic_projection edge to the canonical schema
- Ask for byte_exact across it
- Confirm the route was refused, not silently downgraded


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses an exact relation whose only route is a semantic projection")
step("Register a single semantic_projection edge to the canonical schema")
val registry = a_registry_with_a_lossy_direct_edge()
step("Ask for byte_exact across it")
val resolution = resolve_route(registry, route_request(
    CHROME, CANON, CounterpartRelation.byte_exact, 12, "in-hash"))
step("Confirm the route was refused, not silently downgraded")
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "exact_relation_through_lossy_route")
assert_equal(resolution.route.edges.len(), 0)
```

</details>

#### still permits a non-exact relation across that same projection

- still permits a non-exact relation across that same projection
- Ask for semantic_equal across the projection edge
- Confirm the refusal is about exactness, not about the edge itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("still permits a non-exact relation across that same projection")
step("Ask for semantic_equal across the projection edge")
val registry = a_registry_with_a_lossy_direct_edge()
val resolution = resolve_route(registry, route_request(
    CHROME, CANON, CounterpartRelation.semantic_equal, 12, "in-hash"))
step("Confirm the refusal is about exactness, not about the edge itself")
assert_true(resolution.resolved)
assert_equal(resolution.route.loss_rank, 3)
```

</details>

#### refuses two equal-priority routes rather than picking one

- refuses two equal-priority routes rather than picking one
- Register two distinct single-edge routes with identical loss
- Ask for a route
- Confirm the ambiguity is refused


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses two equal-priority routes rather than picking one")
step("Register two distinct single-edge routes with identical loss")
var registry = converter_registry()
registry = registry_register(registry, converter_manifest(
    "route_a", "1.0.0", CHROME, CANON, ConversionLoss.canonicalizing))
registry = registry_register(registry, converter_manifest(
    "route_b", "1.0.0", CHROME, CANON, ConversionLoss.canonicalizing))
step("Ask for a route")
val resolution = resolve_route(registry, route_request(
    CHROME, CANON, CounterpartRelation.canonical_exact, 12, "in-hash"))
step("Confirm the ambiguity is refused")
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "ambiguous_route")
```

</details>

#### prefers the lower-loss route when the two are not equal-priority

- prefers the lower-loss route when the two are not equal-priority
- Register a lossy route and a lossless route to the same target
- Confirm the lossless route wins without ambiguity


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("prefers the lower-loss route when the two are not equal-priority")
step("Register a lossy route and a lossless route to the same target")
var registry = converter_registry()
registry = registry_register(registry, converter_manifest(
    "lossy", "1.0.0", CHROME, CANON, ConversionLoss.semantic_projection))
registry = registry_register(registry, converter_manifest(
    "clean", "1.0.0", CHROME, CANON, ConversionLoss.representation_only))
step("Confirm the lossless route wins without ambiguity")
val resolution = resolve_route(registry, route_request(
    CHROME, CANON, CounterpartRelation.canonical_exact, 12, "in-hash"))
assert_true(resolution.resolved)
assert_equal(route_edge_ids(resolution.route)[0], "clean")
```

</details>

<details>
<summary>Advanced: refuses a graph that loops before it reaches the target</summary>

#### refuses a graph that loops before it reaches the target

- refuses a graph that loops before it reaches the target
- Register a two-schema cycle with no edge to the target
- Ask for a route to an unreachable canonical schema
- Confirm the cycle is named as such


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a graph that loops before it reaches the target")
step("Register a two-schema cycle with no edge to the target")
var registry = converter_registry()
registry = registry_register(registry, converter_manifest(
    "forward", "1.0.0", CHROME, CHROME_IR, ConversionLoss.identity))
registry = registry_register(registry, converter_manifest(
    "backward", "1.0.0", CHROME_IR, CHROME, ConversionLoss.identity))
step("Ask for a route to an unreachable canonical schema")
val resolution = resolve_route(registry, route_request(
    CHROME, CANON, CounterpartRelation.semantic_equal, 12, "in-hash"))
step("Confirm the cycle is named as such")
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "cycle")
```

</details>


</details>

#### refuses a route that drops a dimension the comparison requires

- refuses a route that drops a dimension the comparison requires
- Register an edge that drops the 'font_fallback' dimension
- Require that dimension in the request
- Confirm the route is refused


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a route that drops a dimension the comparison requires")
step("Register an edge that drops the 'font_fallback' dimension")
var registry = converter_registry()
registry = registry_register(registry, converter_manifest_full(
    "drops_fallback", "1.0.0", CHROME, CANON,
    ConversionLoss.semantic_projection, true,
    ["box_geometry"], ["font_fallback"], []))
step("Require that dimension in the request")
val resolution = resolve_route(registry, route_request_full(
    CHROME, CANON, CounterpartRelation.semantic_equal,
    ["font_fallback"], [], CHROME, 12, "in-hash"))
step("Confirm the route is refused")
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "required_dimension_dropped")
```

</details>

#### refuses a route whose edge assumes an undeclared default

- refuses a route whose edge assumes an undeclared default
- Register an edge that requires a declared 'device_pixel_ratio'
- Resolve without declaring it
- Declare it, and confirm the same route now resolves


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a route whose edge assumes an undeclared default")
step("Register an edge that requires a declared 'device_pixel_ratio'")
var registry = converter_registry()
registry = registry_register(registry, converter_manifest_full(
    "needs_dpr", "1.0.0", CHROME, CANON,
    ConversionLoss.canonicalizing, true,
    [], [], ["default:device_pixel_ratio"]))
step("Resolve without declaring it")
val refused = resolve_route(registry, route_request_full(
    CHROME, CANON, CounterpartRelation.canonical_exact,
    [], [], CHROME, 12, "in-hash"))
assert_false(refused.resolved)
assert_equal(refused.rejection_code, "undeclared_default")
step("Declare it, and confirm the same route now resolves")
val accepted = resolve_route(registry, route_request_full(
    CHROME, CANON, CounterpartRelation.canonical_exact,
    [], ["device_pixel_ratio"], CHROME, 12, "in-hash"))
assert_true(accepted.resolved)
```

</details>

#### refuses a conversion that resolved zero items

- refuses a conversion that resolved zero items
- Ask for a route over an empty input
- Confirm zero items is a refusal, not a vacuous success


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a conversion that resolved zero items")
step("Ask for a route over an empty input")
val registry = a_registry_with_a_clean_two_edge_chain()
val resolution = resolve_route(registry, route_request(
    CHROME, CANON, CounterpartRelation.canonical_exact, 0, "in-hash"))
step("Confirm zero items is a refusal, not a vacuous success")
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "zero_items")
```

</details>

#### refuses a provider whose output schema differs from its manifest

- refuses a provider whose output schema differs from its manifest
- Declare one output schema but present another


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a provider whose output schema differs from its manifest")
step("Declare one output schema but present another")
val registry = a_registry_with_a_clean_two_edge_chain()
val resolution = resolve_route(registry, route_request_full(
    CHROME, CANON, CounterpartRelation.canonical_exact,
    [], [], OTHER, 12, "in-hash"))
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "provider_schema_mismatch")
```

</details>

#### refuses to route at all while the registry holds a rejection

- refuses to route at all while the registry holds a rejection
- Poison the registry with a duplicate registration
- Confirm routing is refused wholesale


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses to route at all while the registry holds a rejection")
step("Poison the registry with a duplicate registration")
var registry = a_registry_with_a_clean_two_edge_chain()
registry = registry_register(registry, converter_manifest(
    "chrome_json_to_ir", "9.9.9", CHROME, CANON, ConversionLoss.identity))
step("Confirm routing is refused wholesale")
val resolution = resolve_route(registry, route_request(
    CHROME, CANON, CounterpartRelation.canonical_exact, 12, "in-hash"))
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "registry_rejected")
```

</details>

#### reports an unreachable target as no_route, distinct from a cycle

- reports an unreachable target as no_route, distinct from a cycle
- Ask for a target nothing points at


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports an unreachable target as no_route, distinct from a cycle")
step("Ask for a target nothing points at")
val registry = a_registry_with_a_clean_two_edge_chain()
val resolution = resolve_route(registry, route_request(
    CHROME, OTHER, CounterpartRelation.semantic_equal, 12, "in-hash"))
assert_false(resolution.resolved)
assert_equal(resolution.rejection_code, "no_route")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`
- **Design:** `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COUNTERPART-F5-001`
- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d54651c297ffb872b9e3e5661a571eb953f2dc4c239ec7619494fbe17428b51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d54651c297ffb872b9e3e5661a571eb953f2dc4c239ec7619494fbe17428b51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d54651c297ffb872b9e3e5661a571eb953f2dc4c239ec7619494fbe17428b51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/infra/counterpart/converter_graph_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/converter_graph_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/infra/counterpart/converter_graph_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/infra/counterpart/converter_graph_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/infra/counterpart/converter_graph_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins a schema version and refuses an unpinned one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/converter_graph_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a well-formed edge and indexes it by its source schema' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/converter_graph_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a second registration of an already-known converter id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
