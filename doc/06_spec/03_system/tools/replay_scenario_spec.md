# Replay Scenario Correlator Specification

Status: **non-admitting historical-seed diagnostic passed**. The coordinator executed 13 cases once: **13 passed, zero failed, zero skipped, zero dropped**, in **224 ms**, exit **0**. No production edit or runtime defect is claimed. This source-synchronized manual is not current Phase1 admission, full CLI, docgen, native, capture or complete replay evidence. Passing cases were not rerun.

Canonical source: `test/03_system/tools/replay_scenario_spec.spl`.
Evidence class: **host-fixture**. Executed inventory: **13 cases**: all 12 original scenarios retained, with stronger payload assertions and one attachment-composition case. These are historical interpreter diagnostic counts, not native binary registration counts.

## Diagnostic evidence and admission boundary

Evidence root: `build/phase-one-storage-gui-diagnostic/`. Execution artifacts: `replay_scenario_spec/cycle-one.{log,rss.env,exit}`; frozen input manifest: `scenario-cycle-one-inputs.sdn`. The resource receipt reports completion, peak process-tree RSS **209468 KiB**, and the coordinator reports quiescence **1**. The canonical source SHA-256 remains `2598916d83de4f790f228da393fb7ac418dd023f6a24069de5fb691c9bb31ef9`.

The historical seed executable remains identical at SHA-256 `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`; retained-generation identity checks passed **7/7**. However, the old mutable `bootstrap.current.env` marker and `bootstrap-preflight.env` record are absent. They were not recreated. Generation integrity identifies the diagnostic producer; it does not grant fresh/current Phase1 admission or replace mandatory current-authority validation. Independent provenance assessment: `/tmp/retained-phase1-seed-provenance-review-20261011.md`.

The source and original `replay_scenario_spec/baseline-plan.sdn` remain frozen as pre-execution inputs. Their UNRUN/planned-admission wording records the original plan and is superseded for actual status by this section and separate `replay_scenario_spec/baseline-status.sdn`. One cycle was used; convergence stops execution without using the remaining two cycles.

## Actual contract and owner

The actual production owner is `src/lib/nogc_sync_mut/replay/semantic/scenario_correlator.spl`. It constructs named correlators, appends ordered steps, associates caller-supplied function patterns and object IDs with valid step indices, and renders summaries. Both `ScenarioCorrelator` and `ScenarioStep` are imported directly from that owner. `std.spec` supplies assertions. The owner's `trace_events` field references `SemanticEvent`; no trace events are supplied or automatically correlated here. The 80% `@cover` value is a target, not measured coverage.

This test operates on real in-memory production objects. It does not read/write trace files, use a live capture stream, assume ordering between independent test scenarios, or qualify automatic event matching. Invalid-index getter/mutator behavior has no selected contract here and is not invented by this repair. No CLI, native or full replay qualification is claimed.

## Manual flow

1. Create a correlator and check its name and initial zero-step state.
2. Add steps, compare names and event bounds, and confirm first/middle/last order.
3. Attach function patterns and compare the actual ordered values as well as counts. Confirm the untargeted step remains unaffected.
4. Attach object IDs and compare their actual ordered values as well as counts.
5. Render scenario summaries and step text; check scenario/name projections, an explicit `Steps: 2` label, and the complete bracketed event-range fragment.
6. Compose both attachment types across two distinct steps in opposite orders. Check the step count before indexed reads, then compare every name, range and attachment array. Require per-step summary counts and ranges to match the retained values.

The additional composition case is justified by the production mutators rebuilding step records: retaining the other attachment type and untargeted step fields is part of the existing attachment contract. No new feature or out-of-range policy is required.

## Preserved legacy obligations

The old canonical and legacy files differ in their documentation, requirement labels, capture annotations, `step(...)` prose and inline oracle comments. Their executable setup, assertions, imports, scenario names and ordering compare exactly after removing only those narrative elements and blank lines. They are **not** full-file byte-identical. All 12 acceptance cases remain in the canonical source; strengthened assertions do not replace existing ones.

| Legacy labels | Retained canonical labels | Existing obligation |
|---|---|---|
| REQ-REPLAY-SCEN-001 | REQ-REPLAY-001, REQ-REPLAY-002 | Name and empty state |
| REQ-REPLAY-SCEN-002 | REQ-REPLAY-003 through REQ-REPLAY-005 | Step insertion, ranges and order |
| REQ-REPLAY-SCEN-003 | REQ-REPLAY-006, REQ-REPLAY-007 | Function association and isolation |
| REQ-REPLAY-SCEN-004 | REQ-REPLAY-008 | Object association |
| REQ-REPLAY-SCEN-005 | REQ-REPLAY-009, REQ-REPLAY-010 | Summary projections |
| REQ-REPLAY-SCEN-006 | REQ-REPLAY-011, REQ-REPLAY-012 | Step text projections |

These are preserved historical scenario labels, not a claim that separate selected requirement documents were found. File admission uses `REQ-SSPEC-SYSTEM`. Prior `statistics`, `protocol_json` and `bit_table` annotations did not provide actual capture artifacts; observations remain assertion-backed without invented capture evidence. Legacy in-memory/no-file/no-cross-scenario-order qualifications are retained. Stale bootstrap command and unconditional rerun instructions are replaced by the coordinator-owned bounded diagnostic workflow.

Additional legacy documentation references are retained for provenance: `doc/01_research/domain/sspec_documentization_maintenance.md`, `doc/03_plan/sspec_modernization_plan.md`, `doc/04_architecture/sspec_documentization_maintenance.md`, and `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md`.

Comparison artifacts: `build/phase-one-storage-gui-diagnostic/replay_scenario_spec/{canonical-original-behavior.spl,legacy-original-behavior.spl}`. Both normalized SHA-256 values are `a643dd163315407a1b797e2ef365a84d8fb64af35aff42d2ad231f6795129df8`. Original canonical SHA-256: `e3da148981c551a00215ae046d8e0cbe809c56ac67bf34b7acd431151fcdeb15`. Original legacy SHA-256: `d4e0c0dcfc2f2afe2ebe35a199ee35f3895cdc7ae8097a615fb821992a1a2e79`. Legacy `test/system/replay_scenario_spec.spl` is removed after this comparison and obligation review.

## Complete executable source

<details>
<summary>Executable SSpec</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @tag:system
# @cover src/lib/nogc_sync_mut/replay/semantic/scenario_correlator.spl 80%
# Coverage is a target, not measured coverage.
# Evidence class: host-fixture; production correlator values and text projection.
# No live capture, automatic trace matching, native or full replay claim.
"""
## Purpose and audience
Covers the ScenarioCorrelator (std.nogc_sync_mut.replay.semantic.scenario_correlator)
used by the sreplay tooling lane to attach steps, matched functions, and matched
object ids to a named replay scenario. Written for engineers changing event
correlation or the scenario summary surface.
## Operator workflow
The coordinator owns the admitted bounded Phase1 diagnostic and its source
manifest. Read the trailing SPEC FILE VERDICT line for actual executed counts.
## Compatibility and limitations
Interpreter-path coverage only; no compiled native lane is exercised here. The
correlator is exercised through its public constructor and mutators, not through
a live capture stream. No trace files are read or written, and no ordering
between independent test scenarios is assumed.
## Verification guidance and troubleshooting
A failed scenario names the correlator operation and checks returned values,
not only counts. This revision is UNRUN; do not infer results from the source
inventory. Do not rerun green scenarios. Invalid-index behavior is unspecified
and remains outside this contract.
"""
# Lifecycle: doc/01_research/ui/capture_replay/llm_first_frame_capture_replay_debugger_2026-06-16.md ;
# doc/03_plan/app/spipe/sspec_scenario_manual_capture_plan.md ;
# doc/04_architecture/app/compiler/pure_simple_profile_guided_executable_optimization_2026-06-01.md ;
# doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md
# @manual_section: replay-scenario-correlator

use std.spec
use std.nogc_sync_mut.replay.semantic.scenario_correlator.{ScenarioStep, ScenarioCorrelator}

describe "ScenarioCorrelator creation":
    it "from_scenario sets scenario_name":
        # @req REQ-REPLAY-001
        # Assertion observation: correlator scenario name retained for review
        step("Create a correlator from a named scenario and read back its name")
        val sc = ScenarioCorrelator.from_scenario("user logs in")
        expect(sc.scenario_name).to_equal("user logs in")

    it "from_scenario starts with zero steps":
        # @req REQ-REPLAY-002
        # Assertion observation: initial step count retained for review
        step("Create a fresh correlator and count its steps")
        val sc = ScenarioCorrelator.from_scenario("checkout flow")
        expect(sc.step_count()).to_equal(0)  # oracle: a fresh correlator has recorded no steps yet

describe "ScenarioCorrelator add_step":
    it "add_step increases step_count":
        # @req REQ-REPLAY-003
        # Assertion observation: post-add step count retained for review
        step("Add one step to the correlator and count steps again")
        var sc = ScenarioCorrelator.from_scenario("login")
        sc.add_step("open login page", 0, 100)
        expect(sc.step_count()).to_equal(1)  # oracle: exactly one add_step call was made

    it "add_step stores step name and event range":
        # @req REQ-REPLAY-004
        # Assertion observation: stored step name and event id range retained for review
        step("Add one step with a bounded event range and read the stored step back")
        var sc = ScenarioCorrelator.from_scenario("login")
        sc.add_step("submit credentials", 100, 250)
        val st = sc.get_step(0)
        expect(st.name).to_equal("submit credentials")
        expect(st.start_event_id).to_equal(100)  # oracle: add_step was given 100 as the range start
        expect(st.end_event_id).to_equal(250)  # oracle: add_step was given 250 as the range end

    it "multiple add_step calls maintain order":
        # @req REQ-REPLAY-005
        # Assertion observation: ordered step names retained for review
        step("Add three steps in sequence and read the first and last back by index")
        var sc = ScenarioCorrelator.from_scenario("purchase")
        sc.add_step("add to cart", 0, 50)
        sc.add_step("checkout", 51, 200)
        sc.add_step("confirm", 201, 300)
        expect(sc.step_count()).to_equal(3)  # oracle: three add_step calls were made in order
        val first = sc.get_step(0)
        expect(first.name).to_equal("add to cart")
        val middle = sc.get_step(1)
        expect(middle.name).to_equal("checkout")
        expect(middle.start_event_id).to_equal(51)
        expect(middle.end_event_id).to_equal(200)
        val last = sc.get_step(2)
        expect(last.name).to_equal("confirm")

describe "ScenarioCorrelator match_functions":
    it "match_functions attaches patterns to a step":
        # @req REQ-REPLAY-006
        # Assertion observation: matched function count retained for review
        step("Attach two function patterns to step 0 and count them")
        var sc = ScenarioCorrelator.from_scenario("login")
        sc.add_step("authenticate", 0, 100)
        sc.match_functions(0, ["auth.login", "auth.verify_password"])
        val st = sc.get_step(0)
        expect(st.matched_functions.len()).to_equal(2)  # oracle: two patterns were passed to match_functions
        expect(st.matched_functions).to_equal(["auth.login", "auth.verify_password"])

    it "match_functions does not affect other steps":
        # @req REQ-REPLAY-007
        # Assertion observation: untargeted step match count retained for review
        step("Attach a pattern to step 0 only and confirm step 1 has no matches")
        var sc = ScenarioCorrelator.from_scenario("multi")
        sc.add_step("step-a", 0, 10)
        sc.add_step("step-b", 11, 20)
        sc.match_functions(0, ["fn_a"])
        val sb = sc.get_step(1)
        expect(sb.matched_functions.len()).to_equal(0)  # oracle: match_functions targeted step 0, not step 1

describe "ScenarioCorrelator match_objects":
    it "match_objects attaches object ids to a step":
        # @req REQ-REPLAY-008
        # Assertion observation: matched object count retained for review
        step("Attach three object ids to step 0 and count them")
        var sc = ScenarioCorrelator.from_scenario("alloc test")
        sc.add_step("allocate user", 0, 50)
        sc.match_objects(0, [101, 102, 103])
        val st = sc.get_step(0)
        expect(st.matched_objects.len()).to_equal(3)  # oracle: three object ids were passed to match_objects
        expect(st.matched_objects).to_equal([101, 102, 103])

describe "ScenarioCorrelator summary":
    it "summary contains scenario name":
        # @req REQ-REPLAY-009
        # Assertion observation: summary text retained for review
        step("Build a correlator summary and read its text")
        var sc = ScenarioCorrelator.from_scenario("dashboard load")
        val out = sc.summary()
        expect(out).to_contain("dashboard load")

    it "summary contains step count":
        # @req REQ-REPLAY-010
        # Assertion observation: summary text with step count retained for review
        step("Add two steps and check the summary reports the count")
        var sc = ScenarioCorrelator.from_scenario("flow")
        sc.add_step("step one", 0, 10)
        sc.add_step("step two", 11, 20)
        val out = sc.summary()
        expect(out).to_contain("2")  # oracle: two steps were added, so the summary must report 2
        expect(out).to_contain("Steps: 2\n")

describe "ScenarioStep to_text":
    it "to_text contains step name":
        # @req REQ-REPLAY-011
        # Assertion observation: rendered step text retained for review
        step("Render a named step and read its text form")
        val st = ScenarioStep(
            name: "render page",
            start_event_id: 10,
            end_event_id: 99,
            matched_functions: [],
            matched_objects: []
        )
        val s = st.to_text()
        expect(s).to_contain("render page")

    it "to_text contains event range":
        # @req REQ-REPLAY-012
        # Assertion observation: rendered event range retained for review
        step("Render a step with a bounded event range and read both bounds back from the text")
        val st = ScenarioStep(
            name: "submit",
            start_event_id: 5,
            end_event_id: 42,
            matched_functions: [],
            matched_objects: []
        )
        val s = st.to_text()
        expect(s).to_contain("5")  # oracle: the step was constructed with start_event_id 5
        expect(s).to_contain("42")  # oracle: the step was constructed with end_event_id 42
        expect(s).to_contain("events=[5..42]")

describe "ScenarioCorrelator attachment composition":
    it "should retain both attachment types and all fields of two distinct steps":
        # @req REQ-SSPEC-SYSTEM
        step("Create two steps and attach functions and objects in opposite orders")
        var sc = ScenarioCorrelator.from_scenario("two stage checkout")
        sc.add_step("authorize", 17, 29)
        sc.add_step("receipt", 31, 47)
        sc.match_functions(0, ["auth.check", "auth.accept"])
        sc.match_objects(1, [301, 302])
        sc.match_objects(0, [101, 102, 103])
        sc.match_functions(1, ["receipt.render"])
        expect(sc.step_count()).to_equal(2)
        if sc.step_count() != 2:
            return
        step("Read both production steps and compare names ranges and every attachment")
        val first = sc.get_step(0)
        expect(first.name).to_equal("authorize")
        expect(first.start_event_id).to_equal(17)
        expect(first.end_event_id).to_equal(29)
        expect(first.matched_functions).to_equal(["auth.check", "auth.accept"])
        expect(first.matched_objects).to_equal([101, 102, 103])
        val second = sc.get_step(1)
        expect(second.name).to_equal("receipt")
        expect(second.start_event_id).to_equal(31)
        expect(second.end_event_id).to_equal(47)
        expect(second.matched_functions).to_equal(["receipt.render"])
        expect(second.matched_objects).to_equal([301, 302])
        step("Require the summary to report each step with its retained counts and ranges")
        val summary = sc.summary()
        expect(summary).to_contain("Scenario: two stage checkout\nSteps: 2\n")
        expect(summary).to_contain("[0] authorize (events 17..29, fns=2, objs=3)")
        expect(summary).to_contain("[1] receipt (events 31..47, fns=1, objs=2)")
```

</details>
