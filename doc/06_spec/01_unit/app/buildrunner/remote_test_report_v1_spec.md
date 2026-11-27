# Remote exact-case report validation acceptance support

**AUTHORED_NOT_RUN.** Authored modern manual; actual compiled SSpec execution
and `spipe-docgen` completeness/zero-stub validation remain pending admitted tools.

Source: `test/01_unit/app/buildrunner/remote_test_report_v1_spec.spl`.
Requirements: RUN-01/RUN-02. Supports AT-RUN-02's report/inventory validation at
the DATA boundary; it does not prove actual test execution or remote acceptance.

## Fixture and evidence boundary

The fixture constructs explicitly synthetic TraceCaseEvent values, task, policy
and pinned TraceRunPlan. It calls the real production
`remote_test_report_from_events_v1` and document entrypoint, including real SDN
encoding/decoding and canonical hash checks. Strings such as `actual alpha` are
fixture labels, not evidence that any framework case ran. No fake runner, remote
process or output publication owner is introduced. No native resource is acquired
and no filesystem cleanup is required.

Ten existing cases retain their original validation assertions. The eleventh
removes all expected/planned cases and all event files. It requires the exact
`REMOTE_EXPECTED_TESTS_REQUIRED` error from both policy encoding and the converter,
so an unrelated plan-hash mismatch cannot mask a vacuous-success regression.
The unchanged task pin deliberately remains valid for the original fixture; empty
policy validation must refuse before comparison against that pin.

## Scenario flow

### Should report only reconciled passing cases in pinned policy order
1. Convert reordered synthetic passing events through the production pinned-report bridge.

### Should require every planned start and terminal observation
1. Remove planned starts or terminal observations and require exact incomplete-inventory refusal.

### Should reject duplicate starts, terminals and emitting files
1. Duplicate starts terminals and source files without changing the pinned plan.

### Should reject unknown case names and events emitted under another path
1. Inject unknown case names and emitting paths into otherwise valid fixture data.

### Should reject failed, pending and skipped outcomes without synthesizing passes
1. Convert failed pending and skipped synthetic outcomes without fabricating passes.

### Should bind the plan run, binary, source and toolchain to the admitted task
1. Change each pinned run binary source and toolchain identity independently.

### Should require the exact canonical plan hash including opaque expectation identity
1. Change or remove the canonical plan hash while preserving other request fields.

### Should require the exact ordered case ID inventory before considering events
1. Change only the ordered case inventory before submitting event observations.

### Should require test action and the original pinned policy
1. Refuse a build policy and an altered previously pinned test policy.

### Should decode real SDN event documents and rejects malformed or noncanonical input
1. Decode actual SDN serialization of synthetic events and reject malformed source.

### Should reject an empty test policy before an empty event set can become a passing report
1. Remove every expected and planned case while preserving the valid task identity.
2. Require the policy boundary's exact zero-inventory refusal before plan hash comparison.

## Production boundary

The converter first binds the policy through `remote_policy_bind_v1`, checks the
plan's run/binary/source/toolchain identity and exact ordered case inventory,
checks canonical plan bytes against task inputs, and reconciles file/case events.
Only complete passed observations yield the exact task-bound report. The pure
report text validator is not a replacement for preceding policy binding; its
acceptance alone does not establish a valid nonempty policy or execution.

The source has eleven registered cases. Counts of source assertions or synthetic
passed observations are not counts of executed tests. Missing/reset/reaping
failures at the actual remote runner, signed Host completion, native ownership,
output digests and parent-only result publication require independent integration
fixtures. This suite does not close full AT-RUN-01 or AT-RUN-02.

<details>
<summary>Executable SSpec source (authored, unexecuted)</summary>

```simple
# codex-system-test
# @req RUN-01 RUN-02
# @acceptance AT-RUN-02
# AUTHORED_NOT_RUN: production report converter, explicitly synthetic trace events.
# No actual test-runner process, remote execution, reset or native reaping proof.
use std.spec.{describe, it, expect, step}
use std.common.build_manager.contracts.{BuildTaskV1, BuildInputV1, builder_task_identity_v1}
use std.common.crypto.sha256.sha256_text
use std.common.traceability.run_plan.{TraceRunPlan, TracePlannedCase, TraceCaseEventFile}
use std.common.traceability.run_plan_codec.encode_trace_run_plan
use std.common.traceability.case_events.{TraceCaseEvent, encode_trace_case_event}
use app.buildrunner.remote_evidence_v1.{RemoteEvidencePolicyV1, remote_policy_encode_v1,
    remote_inventory_digest_v1, remote_test_report_validate_v1}
use app.buildrunner.remote_test_report_v1.*
use test.fixtures.buildrunner.remote_authority_v1.remote_authority_task_v1

struct RemoteReportFixtureV1:
    task: BuildTaskV1
    policy: RemoteEvidencePolicyV1
    plan: TraceRunPlan
    files: [TraceCaseEventFile]

fn report_start_v1(name: text) -> TraceCaseEvent:
    TraceCaseEvent(case_name: name, phase: "started", outcome: "not_finished")

fn report_finish_v1(name: text, outcome: text = "passed") -> TraceCaseEvent:
    TraceCaseEvent(case_name: name, phase: "finished", outcome: outcome)

fn report_fixture_v1() -> RemoteReportFixtureV1:
    var task = remote_authority_task_v1()
    val tools = [BuildInputV1(path: "tools/compiler", digest: sha256_text("pinned compiler"))]
    val policy = RemoteEvidencePolicyV1(host_id: "worker_1", assignment_digest: sha256_text("assignment"),
        controller_epoch: 7, operation_id: "test_operation", action_kind: "test",
        expected_tests: ["case_alpha", "case_beta"], test_report_path: "reports/tests.sdn",
        maximum_bytes: 65536, toolchain_inputs: tools)
    task.toolchain_digest = remote_inventory_digest_v1(tools)
    task.outputs = [policy.test_report_path]
    val plan = TraceRunPlan(run_id: policy.operation_id, subject_id: task.source_digest,
        configuration_id: task.toolchain_digest, expectation_id: "opaque_expectation_1",
        binary_id: task.producer_digest,
        cases: [TracePlannedCase(case_id: "case_alpha", test_path: "test/a_spec.spl",
            case_name: "actual alpha", test_definition_id: "definition_a", lane_id: "native"),
            TracePlannedCase(case_id: "case_beta", test_path: "test/b_spec.spl",
            case_name: "actual beta", test_definition_id: "definition_b", lane_id: "native")])
    task.inputs = [task.inputs[0], tools[0],
        BuildInputV1(path: "remote-policy/" + task.id + ".sdn",
            digest: sha256_text(remote_policy_encode_v1(policy).unwrap())),
        BuildInputV1(path: "remote-tests/" + task.id + ".sdn",
            digest: sha256_text(encode_trace_run_plan(plan).unwrap()))]
    val files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
        events: [report_start_v1("actual alpha"), report_finish_v1("actual alpha")]),
        TraceCaseEventFile(test_path: "test/b_spec.spl",
        events: [report_start_v1("actual beta"), report_finish_v1("actual beta")])]
    RemoteReportFixtureV1(task: task, policy: policy, plan: plan, files: files)

fn report_error_v1(fixture: RemoteReportFixtureV1) -> text:
    match remote_test_report_from_events_v1(fixture.task, fixture.policy, fixture.plan, fixture.files):
        case Ok(report): ""
        case Err(reason): reason

fn report_documents_v1(files: [TraceCaseEventFile]) -> [RemoteTestEventDocumentV1]:
    var documents: [RemoteTestEventDocumentV1] = []
    for file_events in files:
        var encoded: [text] = []
        for event in file_events.events: encoded.push(encode_trace_case_event(event))
        documents.push(RemoteTestEventDocumentV1(test_path: file_events.test_path,
            source: "[" + encoded.join(", ") + "]"))
    documents

describe "remote exact-case report validation from synthetic framework events":
    it "should report only reconciled passing cases in pinned policy order":
        step("Convert reordered synthetic passing events through the production pinned-report bridge")
        val fixture = report_fixture_v1()
        val expected = "SIMPLE-REMOTE-TEST-REPORT-1\n" + builder_task_identity_v1(fixture.task) +
            "\ncase_alpha\tpassed\ncase_beta\tpassed\n"
        val report = remote_test_report_from_events_v1(fixture.task, fixture.policy,
            fixture.plan, [fixture.files[1], fixture.files[0]]).unwrap()
        expect(report).to_equal(expected)
        expect(remote_test_report_validate_v1(fixture.task, fixture.policy, report)).to_equal(Ok(sha256_text(report)))

    it "should require every planned start and terminal observation":
        step("Remove planned starts or terminal observations and require exact incomplete-inventory refusal")
        var fixture = report_fixture_v1()
        fixture.files = []
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_EVENTS_INCOMPLETE")
        fixture = report_fixture_v1()
        fixture.files = [fixture.files[0]]
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_EVENTS_INCOMPLETE")
        fixture = report_fixture_v1()
        fixture.files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
            events: [report_start_v1("actual alpha")]), fixture.files[1]]
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_EVENTS_INCOMPLETE")
        fixture.files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
            events: [report_finish_v1("actual alpha")])]
        expect(report_error_v1(fixture)).to_contain("finished without a start")

    it "should reject duplicate starts, terminals and emitting files":
        step("Duplicate starts terminals and source files without changing the pinned plan")
        var fixture = report_fixture_v1()
        fixture.files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
            events: [report_start_v1("actual alpha"), report_start_v1("actual alpha")])]
        expect(report_error_v1(fixture)).to_contain("duplicate trace case start")
        fixture.files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
            events: [report_start_v1("actual alpha"), report_finish_v1("actual alpha"), report_finish_v1("actual alpha")])]
        expect(report_error_v1(fixture)).to_contain("duplicate trace case terminal")
        fixture = report_fixture_v1()
        fixture.files = [fixture.files[0], fixture.files[0]]
        expect(report_error_v1(fixture)).to_contain("duplicate trace event file")

    it "should reject unknown case names and events emitted under another path":
        step("Inject unknown case names and emitting paths into otherwise valid fixture data")
        var fixture = report_fixture_v1()
        fixture.files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
            events: [report_start_v1("unplanned")])]
        expect(report_error_v1(fixture)).to_contain("unknown trace case")
        fixture.files = [TraceCaseEventFile(test_path: "test/wrong_spec.spl",
            events: [report_start_v1("actual alpha")])]
        expect(report_error_v1(fixture)).to_contain("unknown trace event file")

    it "should reject failed, pending and skipped outcomes without synthesizing passes":
        step("Convert failed pending and skipped synthetic outcomes without fabricating passes")
        var fixture = report_fixture_v1()
        fixture.files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
            events: [report_start_v1("actual alpha"), report_finish_v1("actual alpha", "failed")]), fixture.files[1]]
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_CASE_NOT_PASSED")
        fixture = report_fixture_v1()
        fixture.files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
            events: [report_start_v1("actual alpha"), report_finish_v1("actual alpha", "pending")]), fixture.files[1]]
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_EVENTS_INCOMPLETE")
        fixture = report_fixture_v1()
        fixture.files = [TraceCaseEventFile(test_path: "test/a_spec.spl",
            events: [report_start_v1("actual alpha"), report_finish_v1("actual alpha", "skipped")])]
        expect(report_error_v1(fixture)).to_contain("invalid outcome")

    it "should bind the plan run, binary, source and toolchain to the admitted task":
        step("Change each pinned run binary source and toolchain identity independently")
        val base = report_fixture_v1()
        var run = base.plan
        run.run_id = "another_operation"
        var binary = base.plan
        binary.binary_id = sha256_text("another producer")
        var subject = base.plan
        subject.subject_id = sha256_text("another source")
        var configuration = base.plan
        configuration.configuration_id = sha256_text("another toolchain")
        for plan in [run, binary, subject, configuration]:
            var fixture = base
            fixture.plan = plan
            expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_PLAN_IDENTITY_DIFFERS")

    it "should require the exact canonical plan hash including opaque expectation identity":
        step("Change or remove the canonical plan hash while preserving other request fields")
        var fixture = report_fixture_v1()
        var plan = fixture.plan
        plan.expectation_id = "changed_opaque_expectation"
        fixture.plan = plan
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_PLAN_HASH_DIFFERS")
        fixture = report_fixture_v1()
        var task = fixture.task
        task.inputs = [task.inputs[0], task.inputs[1], task.inputs[2],
            BuildInputV1(path: "remote-tests/" + task.id + ".sdn", digest: sha256_text("wrong plan bytes"))]
        fixture.task = task
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_PLAN_HASH_DIFFERS")
        task.inputs = [task.inputs[0], task.inputs[1], task.inputs[2]]
        fixture.task = task
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_PLAN_NOT_PINNED")

    it "should require the exact ordered case ID inventory before considering events":
        step("Change only the ordered case inventory before submitting event observations")
        var fixture = report_fixture_v1()
        var plan = fixture.plan
        plan.cases = [plan.cases[1], plan.cases[0]]
        fixture.plan = plan
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_PLAN_CASES_DIFFER")
        plan.cases = [plan.cases[0]]
        fixture.plan = plan
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_PLAN_CASES_DIFFER")

    it "should require test action and the original pinned policy":
        step("Refuse a build policy and an altered previously pinned test policy")
        var fixture = report_fixture_v1()
        var policy = fixture.policy
        policy.action_kind = "build"
        fixture.policy = policy
        expect(report_error_v1(fixture)).to_equal("REMOTE_TEST_POLICY_REQUIRED")
        fixture = report_fixture_v1()
        policy = fixture.policy
        policy.controller_epoch = 8
        fixture.policy = policy
        expect(report_error_v1(fixture)).to_equal("REMOTE_POLICY_CHANGED")

    it "should decode real SDN event documents and rejects malformed or noncanonical input":
        step("Decode actual SDN serialization of synthetic events and reject malformed source")
        val fixture = report_fixture_v1()
        val plan_source = encode_trace_run_plan(fixture.plan).unwrap()
        val documents = report_documents_v1(fixture.files)
        val expected = remote_test_report_from_events_v1(fixture.task, fixture.policy,
            fixture.plan, fixture.files).unwrap()
        expect(remote_test_report_from_documents_v1(fixture.task, fixture.policy,
            plan_source, documents)).to_equal(Ok(expected))
        expect(remote_test_report_from_documents_v1(fixture.task, fixture.policy,
            plan_source + "\n", documents)).to_equal(Err("REMOTE_TEST_PLAN_NONCANONICAL"))
        val invalid = [RemoteTestEventDocumentV1(test_path: "test/a_spec.spl", source: "[")]
        expect(remote_test_report_from_documents_v1(fixture.task, fixture.policy,
            plan_source, invalid).is_err()).to_equal(true)

    it "should reject an empty test policy before an empty event set can become a passing report":
        step("Remove every expected and planned case while preserving the valid task identity")
        var fixture = report_fixture_v1()
        var policy = fixture.policy
        policy.expected_tests = []
        fixture.policy = policy
        var plan = fixture.plan
        plan.cases = []
        fixture.plan = plan
        fixture.files = []
        step("Require the policy boundary's exact zero-inventory refusal before plan hash comparison")
        expect(remote_policy_encode_v1(policy)).to_equal(Err("REMOTE_EXPECTED_TESTS_REQUIRED"))
        expect(report_error_v1(fixture)).to_equal("REMOTE_EXPECTED_TESTS_REQUIRED")
```

</details>
