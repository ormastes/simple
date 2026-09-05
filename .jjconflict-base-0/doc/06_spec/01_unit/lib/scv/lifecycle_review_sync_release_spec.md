# lifecycle_review_sync_release_spec

> Proves exact-review, sync-conflict, and immutable-release rules for lifecycle maintainers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_review_sync_release_spec

Proves exact-review, sync-conflict, and immutable-release rules for lifecycle maintainers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/scv/lifecycle_review_sync_release_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Proves exact-review, sync-conflict, and immutable-release rules for lifecycle maintainers.

## Scenarios

### Unified lifecycle admission rules

#### invalidates approval when the reviewed revision changes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- invalidates approval when the reviewed revision changes
   - Expected: stale.state equals `stale_revision`
   - Expected: wrong_head.state equals `rejected_revision`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invalidates approval when the reviewed revision changes")
val review = lifecycle_open_review("REV-1", "chg_1", "rev_base", "rev_head", "integration/main", "standard")
val approval = lifecycle_approval(review, ApprovalEvidence(revision_id: "rev_head", tree_digest: "tree-digest", reviewer: "reviewer", authority: "maintainer", policy_digest: "policy-1", evidence_digest: "evidence-1", created_at: "2026-08-25T00:00:00Z"))
val stale = lifecycle_revalidate_approval(approval, "rev_new", "policy-1", "evidence-1")
expect(stale.state).to_equal("stale_revision")
val wrong_head = lifecycle_approval(review, ApprovalEvidence(revision_id: "rev_other", tree_digest: "tree-digest", reviewer: "reviewer", authority: "maintainer", policy_digest: "policy-1", evidence_digest: "evidence-1", created_at: "2026-08-25T00:00:00Z"))
expect(wrong_head.state).to_equal("rejected_revision")
```

</details>

#### rejects vacuous gate evidence and admits exact evidence

- rejects vacuous gate evidence and admits exact evidence
   - Expected: lifecycle_gate_bundle_admits(rejected, "rev_head").code equals `LIFECYCLE_GATE_INCOMPLETE`
   - Expected: lifecycle_gate_bundle_admits(admitted, "rev_head").status equals `admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects vacuous gate evidence and admits exact evidence")
val review = lifecycle_open_review("REV-2", "chg_2", "rev_base", "rev_head", "integration/main", "standard")
val approval = lifecycle_approval(review, ApprovalEvidence(revision_id: "rev_head", tree_digest: "tree-digest", reviewer: "reviewer", authority: "maintainer", policy_digest: "policy-1", evidence_digest: "evidence-1", created_at: "2026-08-25T00:00:00Z"))
val empty_run = GateRun(gate_run_id: "gate-1", revision_id: "rev_head", gate_id: "tests", policy_digest: "policy-1", tool_digest: "tool-1", environment_digest: "env-1", verdict: "pass", evidence_objects: [])
val rejected = lifecycle_gate_bundle("bundle-1", "rev_head", [empty_run], [approval], "policy-1")
expect(lifecycle_gate_bundle_admits(rejected, "rev_head").code).to_equal("LIFECYCLE_GATE_INCOMPLETE")
val real_run = GateRun(gate_run_id: "gate-2", revision_id: "rev_head", gate_id: "tests", policy_digest: "policy-1", tool_digest: "tool-1", environment_digest: "env-1", verdict: "pass", evidence_objects: ["obj-log"])
val admitted = lifecycle_gate_bundle("bundle-2", "rev_head", [real_run], [approval], "policy-1")
expect(lifecycle_gate_bundle_admits(admitted, "rev_head").status).to_equal("admitted")
```

</details>

#### creates an explicit conflict for concurrent field edits

- creates an explicit conflict for concurrent field edits
   - Expected: plan.action equals `conflict`
   - Expected: event.event_id equals `lifecycle_outbox_id("devhub", "task.updated", "TASK-1", "key-1", "payload-1")`
   - Expected: event.idempotency_key equals `key-1`
   - Expected: event.specversion equals `1.0`
   - Expected: timed.time equals `2026-08-25T00:00:00Z`
   - Expected: timed.data_schema equals `https://schemas.example/devhub/v1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates an explicit conflict for concurrent field edits")
val binding = RemoteBinding(binding_id: "bind-1", entity_type: "task", entity_id: "TASK-1", provider_instance: "jira-prod", remote_kind: "issue", remote_id: "ABC-1", remote_revision: "etag-2", authority_policy_id: "field-split", sync_base_digest: "base-digest", state: "bound")
val plan = lifecycle_sync_field(binding, "status", "open", "implementing", "blocked", "field_split")
expect(plan.action).to_equal("conflict")
expect(lifecycle_record_decode(lifecycle_record_encode(lifecycle_sync_conflict_record(plan.conflict.?))).ok).to_be(true)
expect(lifecycle_outbox_id("devhub", "task.updated", "TASK-1", "key-1", "payload-1")).to_start_with("evt_")
val event = lifecycle_outbox_event("devhub", "task.updated", "TASK-1", "corr-1", "cause-1", "key-1", "payload-1")
expect(event.event_id).to_equal(lifecycle_outbox_id("devhub", "task.updated", "TASK-1", "key-1", "payload-1"))
expect(event.idempotency_key).to_equal("key-1")
expect(event.specversion).to_equal("1.0")
val timed = lifecycle_outbox_event_at("devhub", "task.updated", "TASK-1", "2026-08-25T00:00:00Z", "https://schemas.example/devhub/v1", "corr-1", "cause-1", "key-1", "payload-1")
expect(timed.time).to_equal("2026-08-25T00:00:00Z")
expect(timed.data_schema).to_equal("https://schemas.example/devhub/v1")
```

</details>

#### allows withdrawal but rejects rewriting an immutable publication

- allows withdrawal but rejects rewriting an immutable publication
   - Expected: lifecycle_release_transition(release, "withdrawn").status equals `withdrawn`
   - Expected: lifecycle_release_transition(release, "published").code equals `LIFECYCLE_RELEASE_IMMUTABLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows withdrawal but rejects rewriting an immutable publication")
val release = ReleaseIdentity(release_id: "REL-1", version: "1.4.2", line_id: "simple/1.4", source_revision_id: "rev_head", source_tree_hash: "tree", git_commit_oid: "commit", git_tag_object_oid: "tag-object", gate_bundle_id: "bundle", artifact_set_id: "artifacts", sbom_ids: ["sbom"], provenance_ids: ["prov"], publication_ids: ["github:1"], state: "published", immutable: true)
expect(lifecycle_release_transition(release, "withdrawn").status).to_equal("withdrawn")
expect(lifecycle_release_transition(release, "published").code).to_equal("LIFECYCLE_RELEASE_IMMUTABLE")
```

</details>

#### rejects publication without the complete immutable identity mapping

- rejects publication without the complete immutable identity mapping
   - Expected: lifecycle_release_transition(incomplete, "published").code equals `LIFECYCLE_RELEASE_IDENTITY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects publication without the complete immutable identity mapping")
val incomplete = ReleaseIdentity(release_id: "REL-2", version: "1.4.3", line_id: "simple/1.4", source_revision_id: "rev_head", source_tree_hash: "", git_commit_oid: "", git_tag_object_oid: "tag-object", gate_bundle_id: "bundle", artifact_set_id: "", sbom_ids: [], provenance_ids: [], publication_ids: [], state: "publication_ready", immutable: true)
expect(lifecycle_release_transition(incomplete, "published").code).to_equal("LIFECYCLE_RELEASE_IDENTITY")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-003`
- `REQ-005`
- `REQ-006`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d1ba1ee66b3a3a792631ab86301c87080bf9dc5f3314fb01ee10c87d8aec025`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d1ba1ee66b3a3a792631ab86301c87080bf9dc5f3314fb01ee10c87d8aec025`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d1ba1ee66b3a3a792631ab86301c87080bf9dc5f3314fb01ee10c87d8aec025`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/scv/lifecycle_review_sync_release_spec.spl
mirror: doc/06_spec/01_unit/lib/scv/lifecycle_review_sync_release_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/scv/lifecycle_review_sync_release_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/scv/lifecycle_review_sync_release_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/scv/lifecycle_review_sync_release_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/scv/lifecycle_review_sync_release_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an explicit conflict for concurrent field edits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_review_sync_release_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows withdrawal but rejects rewriting an immutable publication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_review_sync_release_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects publication without the complete immutable identity mapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
