# Counterpart Conformance — provider registry and runner

> The registry decides which providers a conformance run is allowed to draw on,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Conformance — provider registry and runner

The registry decides which providers a conformance run is allowed to draw on,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/provider_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The registry decides which providers a conformance run is allowed to draw on,
and the runner turns a plan into the source bundle the comparison matrix
consumes. This scenario is for the engineer attaching a new provider — a Chrome
build, a SwiftShader worker, a SimpleOS guest — and it shows both what a
well-formed descriptor buys and, more usefully, every descriptor the registry
refuses.

## Scope and Preconditions

No adapter is loaded here. Provider responses are DECLARED STUB ENVELOPES: the
in-process `rt_counterpart_*` ABI shim is not yet linked into the runtime
(doc/08_tracking/bug/counterpart_abi_shim_not_linked_into_runtime_2026-08-09.md),
so the native transport cannot be exercised today. The stub path is parsed by
exactly the same response reader the real transports use, and every stubbed
source records `stubbed:` in its diagnostics, so nothing here can be mistaken
for evidence that a real provider ran.

## Primary Workflow

An operator registers provider descriptors, declares a plan naming a candidate
source and an independent reference, and runs it. The runner executes each
source through the uniform provider interface and hands the bundle to the N-way
engine, whose `rejections` list is the verdict — an empty list means accepted.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Component index | Components indexed by `component_id` and by `counterpart_boundary_id` |
| Independence group | Two wrappers over one engine are ONE reference, not two |
| Unresolved source | A provider that is not registered is `unavailable`, never a pass |
| Non-shrinking matrix | An unavailable source still produces a FAILING cell, not an absent one |
| Provider kind | Chooses the transport; a kind with no Wave-1 transport is unavailable |

## Related Specifications

- `test/01_unit/infra/counterpart/contract_model_spec.spl` — the frozen contracts
- `test/01_unit/infra/counterpart/relation_matrix_spec.spl` — the N-way engine

## Evidence and Provenance

Every rejection asserted below is produced by the registry or the matrix engine
at run time, not restated from the design document. The accepted run at the top
is the control: each refusal scenario differs from it in exactly one respect.

## Recovery and Troubleshooting

A registration rejection names the offending provider and the offending field. A
run rejection names the source and its status. If a run is unexpectedly
accepted, check that the comparison matrix still has as many cells as the plan
declared comparisons — a shrinking matrix is the failure mode this spec exists
to catch.

## Compatibility and Limitations

The `native_in_process` transport is NOT verified: it is blocked on the ABI
shim. The `process_bridge` transport's exit-status mapping is verified as a pure
function; spawning a real bridge executable is out of scope here.

## Scenarios

### Counterpart provider registry

#### accepts two independent providers and indexes their components

- accepts two independent providers and indexes their components
- Register the Simple web provider and the Chrome bridge
- Confirm neither descriptor was refused
   - Expected: provider_registry_provider_count(registry) equals `2`
   - Expected: provider_registry_component_count(registry) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts two independent providers and indexes their components")
step("Register the Simple web provider and the Chrome bridge")
val registry = a_registry_with_two_independent_providers()
step("Confirm neither descriptor was refused")
assert_true(provider_registry_is_clean(registry))
expect(provider_registry_provider_count(registry)).to_equal(2)
expect(provider_registry_component_count(registry)).to_equal(2)
```

</details>

#### answers which providers serve a counterpart boundary

- answers which providers serve a counterpart boundary
- Register both providers against one boundary
- Ask the boundary index who can answer the computed-style boundary
   - Expected: serving.len() equals `2`
- Confirm the two providers are counted as two independent references
   - Expected: groups.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("answers which providers serve a counterpart boundary")
step("Register both providers against one boundary")
val registry = a_registry_with_two_independent_providers()
step("Ask the boundary index who can answer the computed-style boundary")
val serving = provider_registry_components_by_boundary(registry, THE_BOUNDARY)
expect(serving.len()).to_equal(2)
step("Confirm the two providers are counted as two independent references")
val groups = provider_registry_independence_groups_for_boundary(registry, THE_BOUNDARY)
expect(groups.len()).to_equal(2)
```

</details>

#### answers which providers expose a named component

- answers which providers expose a named component
- Register both providers
- Look the Chrome component up by its component identifier
   - Expected: found.len() equals `1`
   - Expected: found[0].provider_id equals `chromium-cft-151`
   - Expected: found[0].independence_group equals `blink`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("answers which providers expose a named component")
step("Register both providers")
val registry = a_registry_with_two_independent_providers()
step("Look the Chrome component up by its component identifier")
val found = provider_registry_components_by_id(registry, "chrome.computed_style")
expect(found.len()).to_equal(1)
expect(found[0].provider_id).to_equal("chromium-cft-151")
expect(found[0].independence_group).to_equal("blink")
```

</details>

#### resolves a plan source to a concrete component

- resolves a plan source to a concrete component
- Register both providers and declare the style plan
- Select the provider for the reference source
- Confirm the selection names the Chrome bridge and its group
   - Expected: selection.provider_id equals `chromium-cft-151`
   - Expected: selection.independence_group equals `blink`
   - Expected: selection.adapter_path equals `build/counterpart/chrome_bridge`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("resolves a plan source to a concrete component")
step("Register both providers and declare the style plan")
val registry = a_registry_with_two_independent_providers()
val plan = the_style_plan()
step("Select the provider for the reference source")
val selection = provider_registry_select(registry, plan.sources[1], plan.boundary_id)
step("Confirm the selection names the Chrome bridge and its group")
assert_true(selection.resolved)
expect(selection.provider_id).to_equal("chromium-cft-151")
expect(selection.independence_group).to_equal("blink")
expect(selection.adapter_path).to_equal("build/counterpart/chrome_bridge")
```

</details>

### Counterpart provider runner

<details>
<summary>Advanced: runs every planned source and accepts an agreeing matrix</summary>

#### runs every planned source and accepts an agreeing matrix

- runs every planned source and accepts an agreeing matrix
- Register two independent providers
- Declare a response envelope for each provider, both agreeing
- Run the plan through the runner and the comparison matrix
- Confirm the run was accepted with one comparison performed
   - Expected: run.rejections.len() equals `0`
   - Expected: run.matrix.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("runs every planned source and accepts an agreeing matrix")
step("Register two independent providers")
val registry = a_registry_with_two_independent_providers()
step("Declare a response envelope for each provider, both agreeing")
val ctx = a_context_with_agreeing_stubs(registry)
step("Run the plan through the runner and the comparison matrix")
val run = runner_run(ctx, the_style_plan())
step("Confirm the run was accepted with one comparison performed")
expect(run.rejections.len()).to_equal(0)
expect(run.matrix.len()).to_equal(1)
assert_true(run.matrix[0].matched)
```

</details>


</details>

#### records a stub marker on every source it did not really execute

- records a stub marker on every source it did not really execute
- Run the plan with declared stub envelopes
- Confirm both sources executed
   - Expected: runner_executed_count(results) equals `2`
   - Expected: runner_unavailable_count(results) equals `0`
- Confirm each result declares that no adapter was invoked


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("records a stub marker on every source it did not really execute")
step("Run the plan with declared stub envelopes")
val ctx = a_context_with_agreeing_stubs(a_registry_with_two_independent_providers())
val results = runner_execute_plan(ctx, the_style_plan())
step("Confirm both sources executed")
expect(runner_executed_count(results)).to_equal(2)
expect(runner_unavailable_count(results)).to_equal(0)
step("Confirm each result declares that no adapter was invoked")
assert_true(results[0].diagnostics.contains(
    "stubbed: declared response, no adapter was invoked"))
assert_true(results[1].diagnostics.contains(
    "stubbed: declared response, no adapter was invoked"))
```

</details>

#### projects a response envelope onto a logical artifact

- projects a response envelope onto a logical artifact
- Read the declared envelope of one component
- Confirm every field was taken from the envelope, not defaulted
   - Expected: artifact.boundary_id equals `THE_BOUNDARY`
   - Expected: artifact.schema_id equals `canonical_style_table`
   - Expected: artifact.schema_version equals `1`
   - Expected: artifact.item_count equals `42`
   - Expected: artifact.canonical_hash equals `bb22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("projects a response envelope onto a logical artifact")
step("Read the declared envelope of one component")
val artifact = counterpart_response_artifact(a_response_envelope("bb22"), THE_BOUNDARY)
step("Confirm every field was taken from the envelope, not defaulted")
expect(artifact.boundary_id).to_equal(THE_BOUNDARY)
expect(artifact.schema_id).to_equal("canonical_style_table")
expect(artifact.schema_version).to_equal(1)
expect(artifact.item_count).to_equal(42)
expect(artifact.canonical_hash).to_equal("bb22")
```

</details>

#### reports a disagreement between two providers as a failed comparison

- reports a disagreement between two providers as a failed comparison
- Declare envelopes whose canonical hashes differ
- Run the plan
- Confirm the disagreement is a rejection, not a tolerance
   - Expected: run.matrix.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports a disagreement between two providers as a failed comparison")
step("Declare envelopes whose canonical hashes differ")
val registry = a_registry_with_two_independent_providers()
var ctx = runner_context(registry, "run-2", "hash-package", "request: computed_style")
val simple_stub = stubbed_response("simple-web", "simple.web.cpu.style", a_response_envelope("aa11"))
val chrome_stub = stubbed_response("chromium-cft-151", "chrome.computed_style", a_response_envelope("zz99"))
ctx = runner_with_stub(ctx, simple_stub)
ctx = runner_with_stub(ctx, chrome_stub)
step("Run the plan")
val run = runner_run(ctx, the_style_plan())
step("Confirm the disagreement is a rejection, not a tolerance")
expect(run.rejections.len()).to_be_greater_than(0)
expect(run.matrix.len()).to_equal(1)
assert_false(run.matrix[0].matched)
```

</details>

### Counterpart provider registration refusals

#### refuses a second descriptor claiming an already-registered provider id

- refuses a second descriptor claiming an already-registered provider id
- Register the Chrome provider
- Register a second descriptor under the same provider id
- Confirm the duplicate was refused and never entered the index
   - Expected: provider_registry_provider_count(registry) equals `1`
   - Expected: provider_registry_component_count(registry) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a second descriptor claiming an already-registered provider id")
step("Register the Chrome provider")
var registry = provider_registry()
registry = provider_registry_register(registry, the_chrome_provider(),
    "build/counterpart/chrome_bridge", "")
step("Register a second descriptor under the same provider id")
registry = provider_registry_register(registry, the_chrome_provider(),
    "build/counterpart/chrome_bridge_other", "")
step("Confirm the duplicate was refused and never entered the index")
assert_false(provider_registry_is_clean(registry))
assert_true(provider_registry_has_rejection_containing(registry,
    "duplicate provider registration 'chromium-cft-151'"))
expect(provider_registry_provider_count(registry)).to_equal(1)
expect(provider_registry_component_count(registry)).to_equal(1)
```

</details>

#### refuses a component whose counterpart boundary identifier is malformed

- refuses a component whose counterpart boundary identifier is malformed
- Declare a provider whose component omits its schema version
- Register it
- Confirm the malformed boundary is refused rather than defaulted to version 1
   - Expected: provider_registry_provider_count(registry) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a component whose counterpart boundary identifier is malformed")
step("Declare a provider whose component omits its schema version")
val malformed = provider_manifest(
    "servo-nightly", ProviderKind.process_bridge, "servo", 1,
    "nightly", "hash-servo", "MPL-2.0",
    [a_style_component("servo.computed_style", "web.resolve.computed_style")]
)
step("Register it")
var registry = provider_registry()
registry = provider_registry_register(registry, malformed, "bin/servo", "")
step("Confirm the malformed boundary is refused rather than defaulted to version 1")
assert_false(provider_registry_is_clean(registry))
assert_true(provider_registry_has_rejection_containing(registry, "invalid boundary id"))
expect(provider_registry_provider_count(registry)).to_equal(0)
```

</details>

#### refuses a descriptor built against a different ABI version

- refuses a descriptor built against a different ABI version
- Declare a provider claiming ABI version 2
- Register it
- Confirm the ABI mismatch is refused, not negotiated down
   - Expected: provider_registry_provider_count(registry) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a descriptor built against a different ABI version")
step("Declare a provider claiming ABI version 2")
val wrong_abi = provider_manifest(
    "servo-nightly", ProviderKind.process_bridge, "servo", 2,
    "nightly", "hash-servo", "MPL-2.0",
    [a_style_component("servo.computed_style", THE_BOUNDARY)]
)
step("Register it")
var registry = provider_registry()
registry = provider_registry_register(registry, wrong_abi, "bin/servo", "")
step("Confirm the ABI mismatch is refused, not negotiated down")
assert_false(provider_registry_is_clean(registry))
assert_true(provider_registry_has_rejection_containing(registry, "abi_version=2"))
expect(provider_registry_provider_count(registry)).to_equal(0)
```

</details>

#### refuses a descriptor that declares no independence group

- refuses a descriptor that declares no independence group
- Declare a provider with an empty independence group
- Register it
- Confirm it is refused: an unattributed provider cannot be counted as independent
   - Expected: provider_registry_provider_count(registry) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a descriptor that declares no independence group")
step("Declare a provider with an empty independence group")
val no_group = provider_manifest(
    "servo-nightly", ProviderKind.process_bridge, "", 1,
    "nightly", "hash-servo", "MPL-2.0",
    [a_style_component("servo.computed_style", THE_BOUNDARY)]
)
step("Register it")
var registry = provider_registry()
registry = provider_registry_register(registry, no_group, "bin/servo", "")
step("Confirm it is refused: an unattributed provider cannot be counted as independent")
assert_false(provider_registry_is_clean(registry))
assert_true(provider_registry_has_rejection_containing(registry,
    "independence_group is empty"))
expect(provider_registry_provider_count(registry)).to_equal(0)
```

</details>

### Counterpart provider selection refusals

#### reports an unregistered provider as unavailable rather than as a pass

- reports an unregistered provider as unavailable rather than as a pass
- Register only the Chrome provider
- Select the provider for a source naming an unregistered Servo build
- Confirm the source resolved to unavailable, with a named reason
   - Expected: provider_status_name(selection.unresolved_status) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports an unregistered provider as unavailable rather than as a pass")
step("Register only the Chrome provider")
var registry = provider_registry()
registry = provider_registry_register(registry, the_chrome_provider(),
    "build/counterpart/chrome_bridge", "")
step("Select the provider for a source naming an unregistered Servo build")
val plan = a_plan_naming_an_unregistered_provider()
val selection = provider_registry_select(registry, plan.sources[0], plan.boundary_id)
step("Confirm the source resolved to unavailable, with a named reason")
assert_false(selection.resolved)
expect(provider_status_name(selection.unresolved_status)).to_equal("unavailable")
expect(selection.diagnostics.len()).to_be_greater_than(0)
```

</details>

#### refuses a component that serves a different counterpart boundary

- refuses a component that serves a different counterpart boundary
- Register a provider whose component serves the layout boundary
- Select it for a plan that names the computed-style boundary
- Confirm the cross-boundary comparison is refused, not silently performed
   - Expected: provider_status_name(selection.unresolved_status) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a component that serves a different counterpart boundary")
step("Register a provider whose component serves the layout boundary")
val other_boundary = provider_manifest(
    "servo-nightly", ProviderKind.process_bridge, "servo", 1,
    "nightly", "hash-servo", "MPL-2.0",
    [a_style_component("servo.layout", "web.spatial_layout.fragment_table@1")]
)
var registry = provider_registry()
registry = provider_registry_register(registry, other_boundary, "bin/servo", "")
step("Select it for a plan that names the computed-style boundary")
val selection = provider_registry_select(registry,
    plan_source("servo", "servo-nightly", "servo.layout",
        OracleAuthority.differential_peer, true),
    THE_BOUNDARY)
step("Confirm the cross-boundary comparison is refused, not silently performed")
assert_false(selection.resolved)
expect(provider_status_name(selection.unresolved_status)).to_equal("unavailable")
```

</details>

### Counterpart run refusals

#### fails the run when a required source is unavailable

- fails the run when a required source is unavailable
- Register only the Chrome provider, leaving the candidate unregistered
- Run a plan whose required candidate names the unregistered provider
- Confirm the run FAILED rather than quietly comparing fewer sources
- Confirm the matrix still has one cell per declared comparison, and it failed
   - Expected: run.matrix.len() equals `plan.comparisons.len()`
- Confirm the unavailable source is still reported, not dropped
   - Expected: run.sources.len() equals `2`
   - Expected: provider_status_name(run.sources[index].status) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("fails the run when a required source is unavailable")
step("Register only the Chrome provider, leaving the candidate unregistered")
var registry = provider_registry()
registry = provider_registry_register(registry, the_chrome_provider(),
    "build/counterpart/chrome_bridge", "")
var ctx = runner_context(registry, "run-3", "hash-package", "request: computed_style")
val chrome_stub = stubbed_response("chromium-cft-151", "chrome.computed_style", a_response_envelope("aa11"))
ctx = runner_with_stub(ctx, chrome_stub)
step("Run a plan whose required candidate names the unregistered provider")
val plan = a_plan_naming_an_unregistered_provider()
val run = runner_run(ctx, plan)
step("Confirm the run FAILED rather than quietly comparing fewer sources")
expect(run.rejections.len()).to_be_greater_than(0)
step("Confirm the matrix still has one cell per declared comparison, and it failed")
expect(run.matrix.len()).to_equal(plan.comparisons.len())
assert_false(run.matrix[0].matched)
step("Confirm the unavailable source is still reported, not dropped")
expect(run.sources.len()).to_equal(2)
val index = runner_result_index(run.sources, "servo")
expect(index).to_be_greater_than(-1)
expect(provider_status_name(run.sources[index].status)).to_equal("unavailable")
```

</details>

#### names the required source in the diagnostics when it did not execute

- names the required source in the diagnostics when it did not execute
- Run the plan whose required candidate is unregistered
- Confirm exactly one source executed and one did not
   - Expected: runner_executed_count(results) equals `1`
   - Expected: runner_unavailable_count(results) equals `1`
- Confirm the failing source is named as REQUIRED in its diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("names the required source in the diagnostics when it did not execute")
step("Run the plan whose required candidate is unregistered")
var registry = provider_registry()
registry = provider_registry_register(registry, the_chrome_provider(),
    "build/counterpart/chrome_bridge", "")
var ctx = runner_context(registry, "run-4", "hash-package", "request: computed_style")
val chrome_stub = stubbed_response("chromium-cft-151", "chrome.computed_style", a_response_envelope("aa11"))
ctx = runner_with_stub(ctx, chrome_stub)
val results = runner_execute_plan(ctx, a_plan_naming_an_unregistered_provider())
step("Confirm exactly one source executed and one did not")
expect(runner_executed_count(results)).to_equal(1)
expect(runner_unavailable_count(results)).to_equal(1)
step("Confirm the failing source is named as REQUIRED in its diagnostics")
val index = runner_result_index(results, "servo")
assert_true(results[index].diagnostics.contains(
    "REQUIRED source servo did not execute: status=unavailable"))
```

</details>

### Counterpart process bridge status mapping

#### maps a clean exit to executed and a non-zero exit to crashed

- maps a clean exit to executed and a non-zero exit to crashed
- Map the exit status of a bridge process that finished cleanly
   - Expected: provider_status_name(process_status_for_exit(0)) equals `executed`
- Map the exit status of a bridge process that aborted
   - Expected: provider_status_name(process_status_for_exit(134)) equals `crashed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("maps a clean exit to executed and a non-zero exit to crashed")
step("Map the exit status of a bridge process that finished cleanly")
expect(provider_status_name(process_status_for_exit(0))).to_equal("executed")
step("Map the exit status of a bridge process that aborted")
expect(provider_status_name(process_status_for_exit(134))).to_equal("crashed")
```

</details>

#### keeps a timeout distinct from a crash

- keeps a timeout distinct from a crash
- Map the exit status of a bridge process killed on its time bound
   - Expected: provider_status_name(process_status_for_exit(124)) equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("keeps a timeout distinct from a crash")
step("Map the exit status of a bridge process killed on its time bound")
expect(provider_status_name(process_status_for_exit(124))).to_equal("timed_out")
```

</details>

#### refuses to guess a missing count in a response envelope

- refuses to guess a missing count in a response envelope
- Read a count the provider never reported
   - Expected: counterpart_response_i64("schema_id: x\n", "item_count") equals `-1`
- Read a count the provider reported with trailing junk
   - Expected: counterpart_response_i64("item_count: 42x\n", "item_count") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses to guess a missing count in a response envelope")
step("Read a count the provider never reported")
expect(counterpart_response_i64("schema_id: x\n", "item_count")).to_equal(-1)
step("Read a count the provider reported with trailing junk")
expect(counterpart_response_i64("item_count: 42x\n", "item_count")).to_equal(-1)
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

- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d9414bbb7f5a3c0add3a150c345b1c99a29d65777724c74d14615959b19674d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d9414bbb7f5a3c0add3a150c345b1c99a29d65777724c74d14615959b19674d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d9414bbb7f5a3c0add3a150c345b1c99a29d65777724c74d14615959b19674d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/infra/counterpart/provider_registry_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/provider_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/infra/counterpart/provider_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/infra/counterpart/provider_registry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/infra/counterpart/provider_registry_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts two independent providers and indexes their components' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/provider_registry_spec.spl:235:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers which providers serve a counterpart boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/provider_registry_spec.spl:247:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers which providers expose a named component' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
