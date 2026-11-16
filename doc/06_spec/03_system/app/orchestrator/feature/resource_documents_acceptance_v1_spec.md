# Configuration and workload document acceptance

**AUTHORED_NOT_RUN.** Manual-only R2 corrects the R1 documentation gap. The executable spec and fixture remain byte-for-byte R1 source. This manual is authored, not docgen output, and supplies no execution or full-row PASS evidence. No production or existing fixture is changed.

[Executable SSpec](../../../../../../test/03_system/app/orchestrator/feature/resource_documents_acceptance_v1_spec.spl) · [exact fixture helper source](../../../../../../test/fixtures/orchestrator_acceptance/resource_documents_v1.spl)

## Shared executable step labels

- `Read the selected configuration and workload fixtures`
- `Decode singleton and combined documents through the production dispatcher`
- `Compare typed values and declaration order`
- `Reject the malformed document at its original source location`

The bounded source helper uses the actual regular-file/no-follow reader with a 1 MiB cap. The list helper only indents complete SDN records. Success-path Result unwraps abort a pure scenario on refusal rather than substituting empty DATA. Shared rejection helpers explicitly fail and return on wrongly accepted malformed input. These tests acquire no process/service owner and perform no launch or apply operation.

## Concrete independently registered flows

### 1. Should preserve configuration-only identities and typed administrative intent

1. Setup: Read host_local_config.sdn and agent_cpu_profile.sdn through the bounded fixture reader; decode their direct HostConfig/Profile values.
2. Action: Build one ResourceList in host/profile order and call decode_resource_set.
3. Oracle: Require exactly 2 items. Compare both singleton identities in order. Match HostConfig then Profile; compare every HostConfig intent field and each CPU/memory range endpoint, GPU and placement flag against the direct decoder. Require host namespace admin and profile namespace caret, preserving child namespaces rather than list-only.
4. Evidence: **NOT_RUN**.

### 2. Should preserve workload-only declaration order across distinct groups and kinds

1. Setup: Read echo_deployment.sdn, ci_job_process.sdn, ci_job_container.sdn and ci_pipeline.sdn.
2. Action: Decode each singleton and one workload-only ResourceList in that order.
3. Oracle: Require 4 ordered identities exactly equal to the singleton identities. The Deployment and process Job both named echo-linux remain distinct by actual group/kind identity.
4. Evidence: **NOT_RUN**.

### 3. Should flatten nested mixed lists without changing singleton identities

1. Setup: Read host/profile plus Deployment/process Job/Pipeline fixtures; build separate configuration and workload lists.
2. Action: Nest both complete lists in one ResourceList; repeat with workload/configuration list order reversed.
3. Oracle: Compare each resulting identity array exactly to the singleton-derived declaration order in both permutations. No item is dropped, regrouped or renamed while flattening.
4. Evidence: **NOT_RUN**.

### 4. Should preserve the complete Deployment template through the unified dispatcher

1. Setup: Read echo_deployment.sdn and call its direct strict decode_resource.
2. Action: Decode the same complete source as one ResourceList child.
3. Oracle: Require one Workload(Deployment) item. Compare metadata name/namespace/labels, replicas, selector labels, template labels and all PodSpec/container/port/resource fields. Additionally require replicas 2, artifactSetRef ci-echo and port 8080.
4. Evidence: **NOT_RUN**.

### 5. Should preserve an explicit Pod document without inventing Deployment defaults

1. Setup: Use the explicit ACCEPTANCE_POD_SOURCE_V1 test document; there is no existing Pod SDN fixture in this selected tree.
2. Action: Call direct decode_resource and unified ResourceList decoding on the exact document.
3. Oracle: Require one Workload(Pod), compare metadata and every PodSpec/container field against direct decode, then require name acceptance-pod, label role=check and runtime native-process. This is supporting Pod DATA evidence, not historical-fixture preservation.
4. Evidence: **NOT_RUN**.

### 6. Should preserve a process Job command arguments and retry policy

1. Setup: Read ci_job_process.sdn and decode_job directly.
2. Action: Decode the same source as one ResourceList child.
3. Oracle: Require one Job, equal metadata/retry policy and full PodSpec fields. Require backoff_limit 0, command [/usr/bin/busybox, echo] and arguments [NONCE-build-linux].
4. Evidence: **NOT_RUN**.

### 7. Should preserve a container Job image command and omitted retry default

1. Setup: Read ci_job_container.sdn, whose backoffLimit is omitted, and decode_job directly.
2. Action: Decode the same source as one ResourceList child.
3. Oracle: Require one Job, equal metadata/retry policy and full PodSpec fields. Require omitted retry default 0, exact busybox image docker.io/library/busybox@sha256:aa and command [/bin/busybox, echo, NONCE-container].
4. Evidence: **NOT_RUN**.

### 8. Should preserve Pipeline declaration order dependencies and run policies

1. Setup: Read ci_pipeline.sdn and decode_pipeline directly.
2. Action: Decode the same complete source as one ResourceList child.
3. Oracle: Require one Pipeline with 4 nodes and default namespace default. Compare metadata labels and each declared node name/template reference/predecessor array/run policy against direct decode. Require first policy on-success, publish predecessors [build-linux, build-probe], and final policy always.
4. Evidence: **NOT_RUN**.

### 9. Should reject a nested duplicate key at the second original key location

1. Setup: Build a ResourceList containing host_local_config.sdn then duplicate_key.sdn.
2. Action: Call decode_resource_set and independently locate the unique complete physical line name: echo-dup.
3. Oracle: Require duplicate_key at spec.items.1.metadata.name, with exact 1-based line/column equal to the physical duplicate key. A wrongly accepted result aborts via unwrap_err rather than supplying a synthetic rejection.
4. Evidence: **NOT_RUN**.

### 10. Should reject a nested unknown field without reparsing away its prefix

1. Setup: Build a ResourceList containing agent_cpu_profile.sdn then unknown_field.sdn.
2. Action: Decode the combined document; independently locate nodeSelector: linux.
3. Oracle: Require unknown_field at spec.items.1.spec.template.spec.nodeSelector and exact physical line/column, preserving the outer child prefix.
4. Evidence: **NOT_RUN**.

### 11. Should reject duplicate identities across nested list boundaries

1. Setup: Read the real process Job source; use it once directly and once inside a nested ResourceList.
2. Action: Invoke the shared rejection helper on the outer list.
3. Oracle: Require duplicate_resource at spec.items.1.spec.items.0.metadata.name, with positive original line and column. The helper explicitly fails and returns if production accepts the document.
4. Evidence: **NOT_RUN**.

### 12. Should reject a bad profile range in the mixed document at its original key

1. Setup: Change only the CPU recommendation in the existing profile from 2000m to 999m; place the process Job before that profile.
2. Action: Decode the mixed ResourceList and independently locate recommend: "999m".
3. Oracle: Require resource_order at spec.items.1.spec.cpu.recommend and exact physical key line/column. This checks nested whole-document rejection rather than a standalone quantity parser.
4. Evidence: **NOT_RUN**.

### 13. Should reject an overflowing host budget without returning the earlier workload

1. Setup: Change host budget CPU 2000m to 999999999999999999999999m; put a valid process Job before the changed HostConfig.
2. Action: Decode the mixed ResourceList and independently locate the changed cpu key.
3. Oracle: Require quantity at spec.items.1.spec.budget.cpu and exact physical line/column. The Result must be Err, exposing no successful earlier-item result.
4. Evidence: **NOT_RUN**.

### 14. Should reject a CI kind that is outside the closed dispatcher variants

1. Setup: Change only the real process Job kind to DaemonSet while retaining its CI apiVersion.
2. Action: Decode it as a ResourceList child via the rejection helper.
3. Oracle: Require unsupported_kind at spec.items.0.kind with positive source line/column; the closed CI dispatcher must not invent another variant.
4. Evidence: **NOT_RUN**.

### 15. Should reject duplicate dependencies before Pipeline expansion

1. Setup: Change the existing Pipeline final predecessor array from [publish] to [publish, publish].
2. Action: Decode that Pipeline as one ResourceList child via the rejection helper.
3. Oracle: Require duplicate_dependency at spec.items.0.spec.jobs.3.runAfter with positive source line/column, before any expansion is attempted.
4. Evidence: **NOT_RUN**.

### 16. Should distinguish successful cyclic document decoding from expansion refusal

1. Setup: Read ci_pipeline_cycle.sdn plus the actual process Job template named echo-linux.
2. Action: Require successful unified decoding to one Pipeline with 2 nodes, then call actual expand_pipeline with that real template.
3. Oracle: Require dependency_cycle at spec.jobs. Require current line=0 and col=0 explicitly: the expander discards spans, so this does not satisfy correct-span acceptance.
4. Evidence: **NOT_RUN**.

### 17. Should refuse a real missing Job reference only when expanding the decoded Pipeline

1. Setup: Read the existing 4-node Pipeline and actual process Job template only.
2. Action: Require unified Pipeline decoding, then call expand_pipeline with only echo-linux available.
3. Oracle: Require unresolved_reference at spec.jobs.1.jobTemplateRef, the first missing echo-probe template. Require current line=0 and col=0; this is a resolver-span gap, not a decode failure.
4. Evidence: **NOT_RUN**.

### 18. Should refuse an undeclared predecessor after its real Job template is supplied

1. Setup: Change the existing cyclic Pipeline first predecessor from b to missing; supply its actual echo-linux Job template.
2. Action: Require successful unified decoding, then call expand_pipeline.
3. Oracle: Require unresolved_reference at spec.jobs.0.runAfter with line=0 and col=0. Template availability and predecessor declaration checks remain distinct.
4. Evidence: **NOT_RUN**.

### 19. Should preserve the existing policy catalog and AgentSession variants in a mixed list

1. Setup: Read caret_policy_catalog.sdn and caret_agent_session.sdn; decode the AgentSession directly.
2. Action: Decode one mixed ResourceList nesting the complete catalog before the session.
3. Oracle: Require 4 items in catalog/session order. Check actual HostPool fields development-linux/caret/linux/aarch64/[podman-rootless]/development and RuntimeClass podman-rootless/caret/podman/linux/aarch64/rootless. Compare all AgentSession metadata, policy references, agent/workspace/terminal-policy fields and full PodSpec against direct decode.
4. Evidence: **NOT_RUN**.

### 20. Should resolve the same static Agent policy from separate and combined snapshots

1. Setup: Read the exact AgentSession and policy catalog snapshots and construct their combined ResourceList.
2. Action: Call actual resolve_agent_policy_v1 on separate source+catalog and combined source+empty catalog for caret/review-simple.
3. Oracle: Compare resolved session/task, profile name/CPU endpoints, pool name/allowed runtimes and runtime name/isolation. Compare each source/catalog digest to SHA256 of the exact supplied bytes, including SHA256 of empty catalog for combined mode. This proves static-policy consistency only.
4. Evidence: **NOT_RUN**.

### 21. Should decode configuration alone without fabricating an executable Agent session

1. Setup: Read the existing policy catalog without an AgentSession.
2. Action: Require unified decode to 3 configuration items, then attempt actual static Agent policy resolution for caret/review-simple.
3. Oracle: Require exact text error agent-session-not-in-source. Successful configuration decoding cannot fabricate an executable session.
4. Evidence: **NOT_RUN**.

### 22. Should refuse a missing static policy reference after the mixed document decodes

1. Setup: Change only AgentSession resourceProfileRef from agent-cpu to missing-profile and combine it with the real catalog.
2. Action: Require unified decode to 4 items, then call actual resolve_agent_policy_v1.
3. Oracle: Require exact text error agent-resource-profile-unresolved. The real resolver returns text, so no source-span oracle or launch permission is implied.
4. Evidence: **NOT_RUN**.

### 23. Should refuse a same-name policy from another namespace

1. Setup: Change catalog namespaces from caret to other while keeping the original caret AgentSession.
2. Action: Require the combined ResourceList decode to 4 items, then call the actual separate source/catalog resolver for caret/review-simple.
3. Oracle: Require exact text error agent-resource-profile-unresolved. Same-name resources in another namespace must not satisfy the session reference; this text-only API cannot prove source spans.
4. Evidence: **NOT_RUN**.

## Full-row limitations and source counters

AT-CFG-01 remains unqualified for generic IaC/general apply-plan resolution. Static Agent policy resolution expressly leaves task/repository/image/CLI capability and authentication unresolved. AT-CFG-02 remains unqualified for correct spans on cycle/reference resolution: Pipeline expansion deliberately returns zero locations and static policy resolution returns text. AT-CFG-03 preserves existing Deployment/Job/Pipeline fixtures and adds explicit Pod DATA; no historical Pod SDN fixture exists in the selected fixture inventory. See CFG_COVERAGE.md for the full original row mapping.

23 registered source scenarios, 177 expectation call sites and 14 fail call sites across the spec/fixture are source counts only. Loop helper call sites may execute multiple times. All compiler, imports, registration, file-read behavior, scenarios and native behavior remain NOT_RUN. No branch coverage, generated-manual evidence or runtime pass is asserted.

## Folded exact executable source

<details>
<summary>Exact 502-line SSpec source — AUTHORED_NOT_RUN — SHA256 fea5fc809f5d24140c4af881638d6e70fda5f0a56269f7fe88b693e69f32b8f6</summary>

```simple
# @req AT-CFG-01 AT-CFG-02 AT-CFG-03
# AUTHORED_NOT_RUN. Decoding and pure Pipeline expansion only: no apply/launch.
use std.spec.*
use test.fixtures.orchestrator_acceptance.resource_documents_v1.*
use std.common.contracts.orchestration.resource_set_v1.*
use std.common.contracts.orchestration.resource_v1.{ResourceV1, PodSpecV1, decode_resource}
use std.common.contracts.orchestration.ci_v1.{decode_job, decode_pipeline, expand_pipeline}
use std.common.contracts.orchestration.profile_v1.decode_resource_profile
use std.common.contracts.orchestration.host_config_v1.decode_host_config
use std.common.contracts.orchestration.agent_session_v1.decode_agent_session
use std.common.contracts.orchestration.agent_policy_resolution_v1.resolve_agent_policy_v1
use std.common.crypto.sha256.sha256_text

val CFG_FIXTURES_V1 = "test/fixtures/orchestration/"

# Only test DATA is read. unwrap propagates a real read/decode failure by aborting
# this pure scenario; it never substitutes an empty resource or resolved value.
fn cfg_source_v1(name: text) -> text:
    acceptance_resource_source_v1(CFG_FIXTURES_V1 + name).unwrap()

fn cfg_identities_v1(source: text) -> [text]:
    val decoded = decode_resource_set(source).unwrap()
    var identities: [text] = []
    for item in decoded.items:
        identities.push(resource_set_item_identity(item))
    identities

# Independently locate one complete physical key line, without using SDN spans.
# A missing or nonunique marker aborts instead of manufacturing a location.
fn cfg_key_position_v1(source: text, marker: text) -> Result<(i64, i64), text>:
    val lines = source.split("\n")
    var row = 0
    var found = 0
    var position = (0, 0)
    for line in lines:
        row = row + 1
        if line.trim() == marker:
            var spaces = 0
            while spaces < line.len() and line.substring(spaces, spaces + 1) == " ":
                spaces = spaces + 1
            position = (row, spaces + 1)
            found = found + 1
    if found != 1:
        return Err("expected exactly one physical key marker")
    Ok(position)

fn cfg_compare_pod_spec_v1(actual: PodSpecV1, direct: PodSpecV1):
    expect(actual.os_name).to_equal(direct.os_name)
    expect(actual.runtime_class).to_equal(direct.runtime_class)
    expect(actual.network_profile).to_equal(direct.network_profile)
    expect(actual.containers.len()).to_equal(direct.containers.len())
    if actual.containers.len() != direct.containers.len(): return
    var index = 0
    while index < direct.containers.len():
        val a = actual.containers[index]
        val d = direct.containers[index]
        expect(a.name).to_equal(d.name)
        expect(a.image).to_equal(d.image)
        expect(a.artifact_set_ref).to_equal(d.artifact_set_ref)
        expect(a.command).to_equal(d.command)
        expect(a.args).to_equal(d.args)
        expect(a.resources.cpu_request_millis).to_equal(d.resources.cpu_request_millis)
        expect(a.resources.cpu_limit_millis).to_equal(d.resources.cpu_limit_millis)
        expect(a.resources.memory_request_bytes).to_equal(d.resources.memory_request_bytes)
        expect(a.resources.memory_limit_bytes).to_equal(d.resources.memory_limit_bytes)
        expect(a.ports.len()).to_equal(d.ports.len())
        if a.ports.len() != d.ports.len(): return
        var port = 0
        while port < d.ports.len():
            expect(a.ports[port].name).to_equal(d.ports[port].name)
            expect(a.ports[port].container_port).to_equal(d.ports[port].container_port)
            port = port + 1
        index = index + 1

describe "Configuration and workload document acceptance":
    # @req AT-CFG-01
    it "should preserve configuration-only identities and typed administrative intent":
        step("Read the selected configuration and workload fixtures")
        val host = cfg_source_v1("host_local_config.sdn")
        val profile = cfg_source_v1("agent_cpu_profile.sdn")
        val direct_host = decode_host_config(host).unwrap()
        val direct_profile = decode_resource_profile(profile).unwrap()
        step("Decode singleton and combined documents through the production dispatcher")
        val combined = decode_resource_set(acceptance_resource_list_v1([host, profile])).unwrap()
        expect(combined.items.len()).to_equal(2)
        if combined.items.len() != 2: return
        step("Compare typed values and declaration order")
        expect(resource_set_item_identity(combined.items[0])).to_equal(cfg_identities_v1(host)[0])
        expect(resource_set_item_identity(combined.items[1])).to_equal(cfg_identities_v1(profile)[0])
        match combined.items[0]:
            case ResourceSetItemV1.HostConfig(actual):
                expect(actual.meta.name).to_equal(direct_host.meta.name)
                expect(actual.meta.ns).to_equal("admin")
                expect(actual.physical_host_id).to_equal(direct_host.physical_host_id)
                expect(actual.service_scope_id).to_equal(direct_host.service_scope_id)
                expect(actual.controller_ref).to_equal(direct_host.controller_ref)
                expect(actual.enrollment_credential_ref).to_equal(direct_host.enrollment_credential_ref)
                expect(actual.runtime_class_ref).to_equal(direct_host.runtime_class_ref)
                expect(actual.journal_root).to_equal(direct_host.journal_root)
                expect(actual.workspace_roots).to_equal(direct_host.workspace_roots)
                expect(actual.cpu_ceiling_millis).to_equal(direct_host.cpu_ceiling_millis)
                expect(actual.memory_ceiling_bytes).to_equal(direct_host.memory_ceiling_bytes)
                expect(actual.exclusive_device_ids).to_equal(direct_host.exclusive_device_ids)
                expect(actual.maintenance_interval_ms).to_equal(direct_host.maintenance_interval_ms)
                expect(actual.maximum_journal_events).to_equal(direct_host.maximum_journal_events)
            case _: fail("configuration item lost its HostConfig variant")
        match combined.items[1]:
            case ResourceSetItemV1.Profile(actual):
                expect(actual.meta.name).to_equal(direct_profile.meta.name)
                expect(actual.meta.ns).to_equal("caret")
                expect(actual.cpu.minimum).to_equal(direct_profile.cpu.minimum)
                expect(actual.cpu.recommended).to_equal(direct_profile.cpu.recommended)
                expect(actual.cpu.preferred).to_equal(direct_profile.cpu.preferred)
                expect(actual.cpu.limit).to_equal(direct_profile.cpu.limit)
                expect(actual.memory.minimum).to_equal(direct_profile.memory.minimum)
                expect(actual.memory.recommended).to_equal(direct_profile.memory.recommended)
                expect(actual.memory.preferred).to_equal(direct_profile.memory.preferred)
                expect(actual.memory.limit).to_equal(direct_profile.memory.limit)
                expect(actual.gpu_required).to_equal(direct_profile.gpu_required)
                expect(actual.preserve_scarce_gpu_hosts).to_equal(direct_profile.preserve_scarce_gpu_hosts)
            case _: fail("configuration item lost its ResourceProfile variant")

    # @req AT-CFG-01 AT-CFG-03
    it "should preserve workload-only declaration order across distinct groups and kinds":
        step("Read the selected configuration and workload fixtures")
        val deployment = cfg_source_v1("echo_deployment.sdn")
        val process = cfg_source_v1("ci_job_process.sdn")
        val container = cfg_source_v1("ci_job_container.sdn")
        val pipeline = cfg_source_v1("ci_pipeline.sdn")
        step("Decode singleton and combined documents through the production dispatcher")
        val identities = cfg_identities_v1(acceptance_resource_list_v1([deployment, process, container, pipeline]))
        step("Compare typed values and declaration order")
        expect(identities).to_equal([cfg_identities_v1(deployment)[0], cfg_identities_v1(process)[0],
            cfg_identities_v1(container)[0], cfg_identities_v1(pipeline)[0]])
        # Deployment and Job both named echo-linux must remain distinct.
        expect(identities.len()).to_equal(4)

    # @req AT-CFG-01
    it "should flatten nested mixed lists without changing singleton identities":
        step("Read the selected configuration and workload fixtures")
        val host = cfg_source_v1("host_local_config.sdn")
        val profile = cfg_source_v1("agent_cpu_profile.sdn")
        val deployment = cfg_source_v1("echo_deployment.sdn")
        val job = cfg_source_v1("ci_job_process.sdn")
        val pipeline = cfg_source_v1("ci_pipeline.sdn")
        step("Decode singleton and combined documents through the production dispatcher")
        val config = acceptance_resource_list_v1([host, profile])
        val workload = acceptance_resource_list_v1([deployment, job, pipeline])
        val mixed = acceptance_resource_list_v1([config, workload])
        step("Compare typed values and declaration order")
        expect(cfg_identities_v1(mixed)).to_equal([cfg_identities_v1(host)[0], cfg_identities_v1(profile)[0],
            cfg_identities_v1(deployment)[0], cfg_identities_v1(job)[0], cfg_identities_v1(pipeline)[0]])
        expect(cfg_identities_v1(acceptance_resource_list_v1([workload, config]))).to_equal([
            cfg_identities_v1(deployment)[0], cfg_identities_v1(job)[0], cfg_identities_v1(pipeline)[0],
            cfg_identities_v1(host)[0], cfg_identities_v1(profile)[0]])

    # @req AT-CFG-03
    it "should preserve the complete Deployment template through the unified dispatcher":
        step("Read the selected configuration and workload fixtures")
        val source = cfg_source_v1("echo_deployment.sdn")
        step("Decode singleton and combined documents through the production dispatcher")
        val direct = decode_resource(source).unwrap()
        val loaded = decode_resource_set(acceptance_resource_list_v1([source])).unwrap()
        expect(loaded.items.len()).to_equal(1)
        if loaded.items.len() != 1: return
        step("Compare typed values and declaration order")
        match (direct, loaded.items[0]):
            case (ResourceV1.Deployment(expected), ResourceSetItemV1.Workload(ResourceV1.Deployment(actual))):
                expect(actual.meta.name).to_equal(expected.meta.name)
                expect(actual.meta.ns).to_equal(expected.meta.ns)
                expect(actual.meta.labels).to_equal(expected.meta.labels)
                expect(actual.replicas).to_equal(expected.replicas)
                expect(actual.selector_labels).to_equal(expected.selector_labels)
                expect(actual.template.labels).to_equal(expected.template.labels)
                cfg_compare_pod_spec_v1(actual.template.spec, expected.template.spec)
                expect(actual.replicas).to_equal(2)
                expect(actual.template.spec.containers[0].artifact_set_ref).to_equal("ci-echo")
                expect(actual.template.spec.containers[0].ports[0].container_port).to_equal(8080)
            case _: fail("direct and unified decoders must both return Deployment")

    # @req AT-CFG-03
    it "should preserve an explicit Pod document without inventing Deployment defaults":
        step("Read the selected configuration and workload fixtures")
        val source = ACCEPTANCE_POD_SOURCE_V1
        step("Decode singleton and combined documents through the production dispatcher")
        val direct = decode_resource(source).unwrap()
        val loaded = decode_resource_set(acceptance_resource_list_v1([source])).unwrap()
        expect(loaded.items.len()).to_equal(1)
        if loaded.items.len() != 1: return
        step("Compare typed values and declaration order")
        match (direct, loaded.items[0]):
            case (ResourceV1.Pod(expected), ResourceSetItemV1.Workload(ResourceV1.Pod(actual))):
                expect(actual.meta.name).to_equal(expected.meta.name)
                expect(actual.meta.ns).to_equal(expected.meta.ns)
                expect(actual.meta.labels).to_equal(expected.meta.labels)
                cfg_compare_pod_spec_v1(actual.spec, expected.spec)
                expect(actual.meta.name).to_equal("acceptance-pod")
                expect(actual.meta.labels["role"]).to_equal("check")
                expect(actual.spec.runtime_class).to_equal("native-process")
            case _: fail("direct and unified decoders must both return Pod")

    # @req AT-CFG-03
    it "should preserve a process Job command arguments and retry policy":
        step("Read the selected configuration and workload fixtures")
        val source = cfg_source_v1("ci_job_process.sdn")
        val direct = decode_job(source).unwrap()
        step("Decode singleton and combined documents through the production dispatcher")
        val loaded = decode_resource_set(acceptance_resource_list_v1([source])).unwrap()
        expect(loaded.items.len()).to_equal(1)
        if loaded.items.len() != 1: return
        step("Compare typed values and declaration order")
        match loaded.items[0]:
            case ResourceSetItemV1.Job(actual):
                expect(actual.meta.name).to_equal(direct.meta.name)
                expect(actual.meta.ns).to_equal(direct.meta.ns)
                expect(actual.meta.labels).to_equal(direct.meta.labels)
                expect(actual.backoff_limit).to_equal(direct.backoff_limit)
                cfg_compare_pod_spec_v1(actual.template, direct.template)
                expect(actual.backoff_limit).to_equal(0)
                expect(actual.template.containers[0].command).to_equal(["/usr/bin/busybox", "echo"])
                expect(actual.template.containers[0].args).to_equal(["NONCE-build-linux"])
            case _: fail("process Job lost its Job variant")

    # @req AT-CFG-03
    it "should preserve a container Job image command and omitted retry default":
        step("Read the selected configuration and workload fixtures")
        val source = cfg_source_v1("ci_job_container.sdn")
        val direct = decode_job(source).unwrap()
        step("Decode singleton and combined documents through the production dispatcher")
        val loaded = decode_resource_set(acceptance_resource_list_v1([source])).unwrap()
        expect(loaded.items.len()).to_equal(1)
        if loaded.items.len() != 1: return
        step("Compare typed values and declaration order")
        match loaded.items[0]:
            case ResourceSetItemV1.Job(actual):
                expect(actual.meta.name).to_equal(direct.meta.name)
                expect(actual.meta.ns).to_equal(direct.meta.ns)
                expect(actual.meta.labels).to_equal(direct.meta.labels)
                expect(actual.backoff_limit).to_equal(direct.backoff_limit)
                cfg_compare_pod_spec_v1(actual.template, direct.template)
                expect(actual.backoff_limit).to_equal(0)
                expect(actual.template.containers[0].image).to_equal("docker.io/library/busybox@sha256:aa")
                expect(actual.template.containers[0].command).to_equal(["/bin/busybox", "echo", "NONCE-container"])
            case _: fail("container Job lost its Job variant")

    # @req AT-CFG-03
    it "should preserve Pipeline declaration order dependencies and run policies":
        step("Read the selected configuration and workload fixtures")
        val source = cfg_source_v1("ci_pipeline.sdn")
        val direct = decode_pipeline(source).unwrap()
        step("Decode singleton and combined documents through the production dispatcher")
        val loaded = decode_resource_set(acceptance_resource_list_v1([source])).unwrap()
        expect(loaded.items.len()).to_equal(1)
        if loaded.items.len() != 1: return
        step("Compare typed values and declaration order")
        match loaded.items[0]:
            case ResourceSetItemV1.Pipeline(actual):
                expect(actual.meta.name).to_equal(direct.meta.name)
                expect(actual.meta.ns).to_equal("default")
                expect(actual.meta.labels).to_equal(direct.meta.labels)
                expect(actual.jobs.len()).to_equal(4)
                if actual.jobs.len() != 4: return
                var index = 0
                while index < actual.jobs.len():
                    expect(actual.jobs[index].name).to_equal(direct.jobs[index].name)
                    expect(actual.jobs[index].job_template_ref).to_equal(direct.jobs[index].job_template_ref)
                    expect(actual.jobs[index].run_after).to_equal(direct.jobs[index].run_after)
                    expect(actual.jobs[index].run_policy).to_equal(direct.jobs[index].run_policy)
                    index = index + 1
                expect(actual.jobs[0].run_policy).to_equal("on-success")
                expect(actual.jobs[2].run_after).to_equal(["build-linux", "build-probe"])
                expect(actual.jobs[3].run_policy).to_equal("always")
            case _: fail("Pipeline lost its Pipeline variant")

    # @req AT-CFG-02
    it "should reject a nested duplicate key at the second original key location":
        val source = acceptance_resource_list_v1([cfg_source_v1("host_local_config.sdn"),
            cfg_source_v1("duplicate_key.sdn")])
        step("Reject the malformed document at its original source location")
        val error = decode_resource_set(source).unwrap_err()
        val position = cfg_key_position_v1(source, "name: echo-dup").unwrap()
        expect(error.kind).to_equal("duplicate_key")
        expect(error.path).to_equal("spec.items.1.metadata.name")
        expect(error.line).to_equal(position.0)
        expect(error.col).to_equal(position.1)

    # @req AT-CFG-02
    it "should reject a nested unknown field without reparsing away its prefix":
        val source = acceptance_resource_list_v1([cfg_source_v1("agent_cpu_profile.sdn"),
            cfg_source_v1("unknown_field.sdn")])
        step("Reject the malformed document at its original source location")
        val error = decode_resource_set(source).unwrap_err()
        val position = cfg_key_position_v1(source, "nodeSelector: linux").unwrap()
        expect(error.kind).to_equal("unknown_field")
        expect(error.path).to_equal("spec.items.1.spec.template.spec.nodeSelector")
        expect(error.line).to_equal(position.0)
        expect(error.col).to_equal(position.1)

    # @req AT-CFG-02
    it "should reject duplicate identities across nested list boundaries":
        val job = cfg_source_v1("ci_job_process.sdn")
        val source = acceptance_resource_list_v1([job, acceptance_resource_list_v1([job])])
        step("Reject the malformed document at its original source location")
        acceptance_resource_error_v1(source, "duplicate_resource", "spec.items.1.spec.items.0.metadata.name")

    # @req AT-CFG-02
    it "should reject a bad profile range in the mixed document at its original key":
        val profile = cfg_source_v1("agent_cpu_profile.sdn").replace("recommend: \"2000m\"", "recommend: \"999m\"")
        val source = acceptance_resource_list_v1([cfg_source_v1("ci_job_process.sdn"), profile])
        step("Reject the malformed document at its original source location")
        val error = decode_resource_set(source).unwrap_err()
        val position = cfg_key_position_v1(source, "recommend: \"999m\"").unwrap()
        expect(error.kind).to_equal("resource_order")
        expect(error.path).to_equal("spec.items.1.spec.cpu.recommend")
        expect(error.line).to_equal(position.0)
        expect(error.col).to_equal(position.1)

    # @req AT-CFG-02
    it "should reject an overflowing host budget without returning the earlier workload":
        val host = cfg_source_v1("host_local_config.sdn").replace("cpu: 2000m", "cpu: 999999999999999999999999m")
        val source = acceptance_resource_list_v1([cfg_source_v1("ci_job_process.sdn"), host])
        step("Reject the malformed document at its original source location")
        val error = decode_resource_set(source).unwrap_err()
        val position = cfg_key_position_v1(source, "cpu: 999999999999999999999999m").unwrap()
        expect(error.kind).to_equal("quantity")
        expect(error.path).to_equal("spec.items.1.spec.budget.cpu")
        expect(error.line).to_equal(position.0)
        expect(error.col).to_equal(position.1)

    # @req AT-CFG-02
    it "should reject a CI kind that is outside the closed dispatcher variants":
        val source = cfg_source_v1("ci_job_process.sdn").replace("kind: Job", "kind: DaemonSet")
        step("Reject the malformed document at its original source location")
        acceptance_resource_error_v1(acceptance_resource_list_v1([source]), "unsupported_kind", "spec.items.0.kind")

    # @req AT-CFG-02
    it "should reject duplicate dependencies before Pipeline expansion":
        val pipeline = cfg_source_v1("ci_pipeline.sdn").replace("runAfter: [publish]", "runAfter: [publish, publish]")
        step("Reject the malformed document at its original source location")
        acceptance_resource_error_v1(acceptance_resource_list_v1([pipeline]), "duplicate_dependency", "spec.items.0.spec.jobs.3.runAfter")

    # @req AT-CFG-02
    it "should distinguish successful cyclic document decoding from expansion refusal":
        val source = cfg_source_v1("ci_pipeline_cycle.sdn")
        val job = decode_job(cfg_source_v1("ci_job_process.sdn")).unwrap()
        step("Decode singleton and combined documents through the production dispatcher")
        val loaded = decode_resource_set(acceptance_resource_list_v1([source])).unwrap()
        expect(loaded.items.len()).to_equal(1)
        if loaded.items.len() != 1: return
        step("Compare typed values and declaration order")
        match loaded.items[0]:
            case ResourceSetItemV1.Pipeline(pipeline):
                expect(pipeline.jobs.len()).to_equal(2)
                val error = expand_pipeline(pipeline, {"echo-linux": job}).unwrap_err()
                expect(error.kind).to_equal("dependency_cycle")
                expect(error.path).to_equal("spec.jobs")
                # Current expander intentionally has no source map. This is a
                # measured contract limitation, not correct-span acceptance.
                expect(error.line).to_equal(0)
                expect(error.col).to_equal(0)
            case _: fail("cyclic Pipeline must decode before reference expansion")

    # @req AT-CFG-02
    it "should refuse a real missing Job reference only when expanding the decoded Pipeline":
        val source = cfg_source_v1("ci_pipeline.sdn")
        val job = decode_job(cfg_source_v1("ci_job_process.sdn")).unwrap()
        step("Decode singleton and combined documents through the production dispatcher")
        val loaded = decode_resource_set(acceptance_resource_list_v1([source])).unwrap()
        expect(loaded.items.len()).to_equal(1)
        if loaded.items.len() != 1: return
        step("Compare typed values and declaration order")
        match loaded.items[0]:
            case ResourceSetItemV1.Pipeline(pipeline):
                val error = expand_pipeline(pipeline, {"echo-linux": job}).unwrap_err()
                expect(error.kind).to_equal("unresolved_reference")
                expect(error.path).to_equal("spec.jobs.1.jobTemplateRef")
                expect(error.line).to_equal(0)
                expect(error.col).to_equal(0)
            case _: fail("Pipeline must remain typed until template resolution")

    # @req AT-CFG-02
    it "should refuse an undeclared predecessor after its real Job template is supplied":
        val source = cfg_source_v1("ci_pipeline_cycle.sdn").replace("runAfter: [b]", "runAfter: [missing]")
        val job = decode_job(cfg_source_v1("ci_job_process.sdn")).unwrap()
        step("Decode singleton and combined documents through the production dispatcher")
        val loaded = decode_resource_set(acceptance_resource_list_v1([source])).unwrap()
        expect(loaded.items.len()).to_equal(1)
        if loaded.items.len() != 1: return
        step("Compare typed values and declaration order")
        match loaded.items[0]:
            case ResourceSetItemV1.Pipeline(pipeline):
                val error = expand_pipeline(pipeline, {"echo-linux": job}).unwrap_err()
                expect(error.kind).to_equal("unresolved_reference")
                expect(error.path).to_equal("spec.jobs.0.runAfter")
                expect(error.line).to_equal(0)
                expect(error.col).to_equal(0)
            case _: fail("Pipeline must remain typed until predecessor resolution")

    # @req AT-CFG-01
    it "should preserve the existing policy catalog and AgentSession variants in a mixed list":
        step("Read the selected configuration and workload fixtures")
        val catalog = cfg_source_v1("caret_policy_catalog.sdn")
        val session = cfg_source_v1("caret_agent_session.sdn")
        val direct = decode_agent_session(session).unwrap()
        step("Decode singleton and combined documents through the production dispatcher")
        val combined = decode_resource_set(acceptance_resource_list_v1([catalog, session])).unwrap()
        expect(combined.items.len()).to_equal(4)
        if combined.items.len() != 4: return
        step("Compare typed values and declaration order")
        match combined.items[1]:
            case ResourceSetItemV1.HostPool(pool):
                expect(pool.meta.name).to_equal("development-linux")
                expect(pool.meta.ns).to_equal("caret")
                expect(pool.execution_os).to_equal("linux")
                expect(pool.architecture).to_equal("aarch64")
                expect(pool.runtime_class_refs).to_equal(["podman-rootless"])
                expect(pool.trust_class).to_equal("development")
            case _: fail("catalog HostPool must retain its variant and position")
        match combined.items[2]:
            case ResourceSetItemV1.RuntimeClass(runtime):
                expect(runtime.meta.name).to_equal("podman-rootless")
                expect(runtime.meta.ns).to_equal("caret")
                expect(runtime.provider).to_equal("podman")
                expect(runtime.execution_os).to_equal("linux")
                expect(runtime.architecture).to_equal("aarch64")
                expect(runtime.isolation).to_equal("rootless")
            case _: fail("catalog RuntimeClass must retain its variant and position")
        match combined.items[3]:
            case ResourceSetItemV1.AgentSession(actual):
                expect(actual.meta.name).to_equal(direct.meta.name)
                expect(actual.meta.ns).to_equal(direct.meta.ns)
                expect(actual.meta.labels).to_equal(direct.meta.labels)
                expect(actual.resource_profile_ref).to_equal(direct.resource_profile_ref)
                expect(actual.host_pool_ref).to_equal(direct.host_pool_ref)
                expect(actual.runtime_class_ref).to_equal(direct.runtime_class_ref)
                expect(actual.agent.provider).to_equal(direct.agent.provider)
                expect(actual.agent.task_ref).to_equal(direct.agent.task_ref)
                expect(actual.workspace.repository_ref).to_equal(direct.workspace.repository_ref)
                expect(actual.workspace.revision_ref).to_equal(direct.workspace.revision_ref)
                expect(actual.workspace.isolation).to_equal(direct.workspace.isolation)
                expect(actual.workspace.retention).to_equal(direct.workspace.retention)
                expect(actual.session.frontend).to_equal(direct.session.frontend)
                expect(actual.session.persistent).to_equal(direct.session.persistent)
                expect(actual.session.disconnect_policy).to_equal(direct.session.disconnect_policy)
                cfg_compare_pod_spec_v1(actual.template, direct.template)
            case _: fail("AgentSession must retain its variant and position")

    # @req AT-CFG-01
    it "should resolve the same static Agent policy from separate and combined snapshots":
        step("Read the selected configuration and workload fixtures")
        val catalog = cfg_source_v1("caret_policy_catalog.sdn")
        val session = cfg_source_v1("caret_agent_session.sdn")
        val combined = acceptance_resource_list_v1([catalog, session])
        step("Decode singleton and combined documents through the production dispatcher")
        val separate = resolve_agent_policy_v1(session, catalog, "caret", "review-simple").unwrap()
        val together = resolve_agent_policy_v1(combined, "", "caret", "review-simple").unwrap()
        step("Compare typed values and declaration order")
        expect(together.session.meta.name).to_equal(separate.session.meta.name)
        expect(together.session.agent.task_ref).to_equal(separate.session.agent.task_ref)
        expect(together.profile.meta.name).to_equal(separate.profile.meta.name)
        expect(together.profile.cpu.minimum).to_equal(separate.profile.cpu.minimum)
        expect(together.profile.cpu.limit).to_equal(separate.profile.cpu.limit)
        expect(together.pool.meta.name).to_equal(separate.pool.meta.name)
        expect(together.pool.runtime_class_refs).to_equal(separate.pool.runtime_class_refs)
        expect(together.runtime.meta.name).to_equal(separate.runtime.meta.name)
        expect(together.runtime.isolation).to_equal(separate.runtime.isolation)
        expect(separate.source_digest).to_equal(sha256_text(session))
        expect(separate.catalog_digest).to_equal(sha256_text(catalog))
        expect(together.source_digest).to_equal(sha256_text(combined))
        expect(together.catalog_digest).to_equal(sha256_text(""))

    # @req AT-CFG-01
    it "should decode configuration alone without fabricating an executable Agent session":
        val catalog = cfg_source_v1("caret_policy_catalog.sdn")
        step("Decode singleton and combined documents through the production dispatcher")
        val decoded = decode_resource_set(catalog).unwrap()
        expect(decoded.items.len()).to_equal(3)
        step("Compare typed values and declaration order")
        val error = resolve_agent_policy_v1(catalog, "", "caret", "review-simple").unwrap_err()
        expect(error).to_equal("agent-session-not-in-source")

    # @req AT-CFG-02
    it "should refuse a missing static policy reference after the mixed document decodes":
        val catalog = cfg_source_v1("caret_policy_catalog.sdn")
        val session = cfg_source_v1("caret_agent_session.sdn").replace("resourceProfileRef: agent-cpu", "resourceProfileRef: missing-profile")
        val combined = acceptance_resource_list_v1([catalog, session])
        step("Decode singleton and combined documents through the production dispatcher")
        expect(decode_resource_set(combined).unwrap().items.len()).to_equal(4)
        step("Compare typed values and declaration order")
        val error = resolve_agent_policy_v1(combined, "", "caret", "review-simple").unwrap_err()
        expect(error).to_equal("agent-resource-profile-unresolved")
        # The real resolver returns text, so no source-span claim is made.

    # @req AT-CFG-02
    it "should refuse a same-name policy from another namespace":
        val catalog = cfg_source_v1("caret_policy_catalog.sdn").replace("namespace: caret", "namespace: other")
        val session = cfg_source_v1("caret_agent_session.sdn")
        step("Decode singleton and combined documents through the production dispatcher")
        expect(decode_resource_set(acceptance_resource_list_v1([catalog, session])).unwrap().items.len()).to_equal(4)
        step("Compare typed values and declaration order")
        val error = resolve_agent_policy_v1(session, catalog, "caret", "review-simple").unwrap_err()
        expect(error).to_equal("agent-resource-profile-unresolved")
```

</details>
