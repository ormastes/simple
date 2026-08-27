# lifecycle_entity_codec_spec

> Typed lifecycle codecs preserve every declared field and reject kind mismatches.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_entity_codec_spec

Typed lifecycle codecs preserve every declared field and reject kind mismatches.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/scv/lifecycle_entity_codec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Typed lifecycle codecs preserve every declared field and reject kind mismatches.

## Scenarios

### Typed SCV lifecycle entity codecs

#### round trips change and immutable revision fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round trips change and immutable revision fields
   - Expected: change_record(change_from_record(change_wire).?).fields equals `change_wire.fields`
   - Expected: revision_record(revision_from_record(revision_wire).?).fields equals `revision_wire.fields`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round trips change and immutable revision fields")
val change = ChangeIdentity(change_id: "CHG-1", title: "title", intent_digest: "intent", owner: "owner")
val change_wire = _wire(change_record(change))
expect(change_record(change_from_record(change_wire).?).fields).to_equal(change_wire.fields)
val foreign = LifecycleRecord(schema: "foreign/1", kind: change_wire.kind, entity_id: change_wire.entity_id, fields: change_wire.fields, digest: change_wire.digest)
expect(change_from_record(foreign)).to_be_nil()
expect(change_from_record(lifecycle_record("change", "CHG-DUP", ["title=first", "title=second", "intent_digest=intent", "owner=owner"]))).to_be_nil()
expect(change_from_record(lifecycle_record("change", "CHG-UNKNOWN", ["title=title", "intent_digest=intent", "owner=owner", "surprise=value"]))).to_be_nil()
expect(change_from_record(revision_record(RevisionIdentity(revision_id: "REV-X", change_id: "CHG-1", tree_id: "tree", parent_revision_ids: [], metadata_digest: "meta", aliases: RevisionAliases(jj_change_id: "", jj_commit_id: "", git_oid: "", provider_patchsets: []))))).to_be_nil()
val revision = RevisionIdentity(revision_id: "REV-1", change_id: "CHG-1", tree_id: "tree", parent_revision_ids: ["REV-0", "REV-A"], metadata_digest: "meta", aliases: RevisionAliases(jj_change_id: "jj-change", jj_commit_id: "jj-commit", git_oid: "git", provider_patchsets: ["gh:1", "gerrit:2"]))
val revision_wire = _wire(revision_record(revision))
expect(revision_record(revision_from_record(revision_wire).?).fields).to_equal(revision_wire.fields)
```

</details>

#### round trips review finding approval and gate fields

- round trips review finding approval and gate fields
   - Expected: review_session_record(review_session_from_record(session_wire).?).fields equals `session_wire.fields`
   - Expected: review_run_record(review_run_from_record(run_wire).?).fields equals `run_wire.fields`
   - Expected: finding_record(finding_from_record(finding_wire).?).fields equals `finding_wire.fields`
   - Expected: approval_record(approval_from_record(approval_wire).?).fields equals `approval_wire.fields`
   - Expected: gate_run_record(gate_run_from_record(gate_wire).?).fields equals `gate_wire.fields`
   - Expected: gate_bundle_record(gate_bundle_from_record(bundle_wire).?).fields equals `bundle_wire.fields`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round trips review finding approval and gate fields")
val session = ReviewSession(review_id: "REVIEW-1", change_id: "CHG-1", base_revision_id: "REV-0", head_revision_id: "REV-1", target_ref: "integration/main", profile: "standard", state: "reviewing")
val session_wire = _wire(review_session_record(session))
expect(review_session_record(review_session_from_record(session_wire).?).fields).to_equal(session_wire.fields)
val run = ReviewRun(review_run_id: "RUN-1", review_id: "REVIEW-1", parent_run_id: "RUN-0", reviewer: "reviewer", reviewer_version: "v1", role: "security", policy_digest: "policy", evidence_bundle_id: "evidence", verdict: "escalate", unresolved_question_ids: ["Q1", "Q2"])
val run_wire = _wire(review_run_record(run))
expect(review_run_record(review_run_from_record(run_wire).?).fields).to_equal(run_wire.fields)
val anchor = SourceAnchor(path: "src/a.spl", parser: "simple", symbol_id: "sym", syntax_node_kind: "call", syntax_node_fingerprint: "node", surrounding_token_hash: "tokens", semantic_entity_id: "entity", fallback_line: 42, fallback_column: 7)
val finding = Finding(finding_id: "FIND-1", review_id: "REVIEW-1", revision_id: "REV-1", producer_run_id: "RUN-1", rule_id: "RULE-1", category: "security", severity: "high", confidence_evidence: "calibrated", source_anchor: anchor, fingerprint: "fingerprint", message: "message=retained", evidence_refs: ["E1", "E2"], state: "open")
val finding_wire = _wire(finding_record(finding))
expect(finding_record(finding_from_record(finding_wire).?).fields).to_equal(finding_wire.fields)
val approval = Approval(approval_id: "APR-1", review_id: "REVIEW-1", revision_id: "REV-1", tree_digest: "tree", reviewer: "reviewer", authority: "maintainer", policy_digest: "policy", evidence_bundle_digest: "evidence", created_at: "time", state: "approved")
val approval_wire = _wire(approval_record(approval))
expect(approval_record(approval_from_record(approval_wire).?).fields).to_equal(approval_wire.fields)
val gate = GateRun(gate_run_id: "GATE-1", revision_id: "REV-1", gate_id: "tests", policy_digest: "policy", tool_digest: "tool", environment_digest: "env", verdict: "pass", evidence_objects: ["OBJ-1", "OBJ-2"])
val gate_wire = _wire(gate_run_record(gate))
expect(gate_run_record(gate_run_from_record(gate_wire).?).fields).to_equal(gate_wire.fields)
val bundle = GateBundle(gate_bundle_id: "BUNDLE-1", revision_id: "REV-1", gate_run_ids: ["GATE-1"], approval_ids: ["APR-1"], complete: true, bundle_digest: "bundle", policy_digest: "policy")
val bundle_wire = _wire(gate_bundle_record(bundle))
expect(gate_bundle_record(gate_bundle_from_record(bundle_wire).?).fields).to_equal(bundle_wire.fields)
```

</details>

#### round trips work sync publication and audit fields

- round trips work sync publication and audit fields
   - Expected: remote_binding_record(remote_binding_from_record(binding_wire).?).fields equals `binding_wire.fields`
   - Expected: sync_conflict_record_typed(sync_conflict_from_record(conflict_wire).?).fields equals `conflict_wire.fields`
   - Expected: feature_record_typed(feature_from_record(feature_wire).?).fields equals `feature_wire.fields`
   - Expected: task_record(task_from_record(task_wire).?).fields equals `task_wire.fields`
   - Expected: run_record(run_from_record(lifecycle_run_wire).?).fields equals `lifecycle_run_wire.fields`
   - Expected: audit_record_typed(audit_from_record(audit_wire).?).fields equals `audit_wire.fields`
   - Expected: publication_record(publication_from_record(publication_wire).?).fields equals `publication_wire.fields`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round trips work sync publication and audit fields")
val binding = RemoteBinding(binding_id: "BIND-1", entity_type: "task", entity_id: "TASK-1", provider_instance: "jira", remote_kind: "issue", remote_id: "ABC-1", remote_revision: "etag", authority_policy_id: "split", sync_base_digest: "base", state: "bound")
val binding_wire = _wire(remote_binding_record(binding))
expect(remote_binding_record(remote_binding_from_record(binding_wire).?).fields).to_equal(binding_wire.fields)
val conflict = SyncConflict(conflict_id: "CONFLICT-1", binding_id: "BIND-1", field: "status", base_value: "open", local_value: "doing", remote_value: "blocked", policy: "split", state: "open")
val conflict_wire = _wire(sync_conflict_record_typed(conflict))
expect(sync_conflict_record_typed(sync_conflict_from_record(conflict_wire).?).fields).to_equal(conflict_wire.fields)
val feature = Feature(feature_id: "FEAT-1", title: "feature", state: "implementing", owner: "team", goal: "goal", acceptance_ids: ["AC-1", "AC-2"], document_paths: ["doc/a", "doc/b"], task_ids: ["TASK-1"])
val feature_wire = _wire(feature_record_typed(feature))
expect(feature_record_typed(feature_from_record(feature_wire).?).fields).to_equal(feature_wire.fields)
val task = Task(task_id: "TASK-1", feature_id: "FEAT-1", title: "task", state: "open", owner: "agent", change_ids: ["CHG-1", "CHG-2"])
val task_wire = _wire(task_record(task))
expect(task_record(task_from_record(task_wire).?).fields).to_equal(task_wire.fields)
val lifecycle_run = LifecycleRun(run_id: "EXEC-1", feature_id: "FEAT-1", task_id: "TASK-1", change_id: "CHG-1", base_revision_id: "REV-0", state: "running")
val lifecycle_run_wire = _wire(run_record(lifecycle_run))
expect(run_record(run_from_record(lifecycle_run_wire).?).fields).to_equal(lifecycle_run_wire.fields)
val audit = OperationAudit(operation_id: "OP-1", operation_kind: "integrate", entity_id: "CHG-1", actor: "agent", authority: "maintainer", policy_digest: "policy", input_digest: "input", output_digest: "output", state: "planned")
val audit_wire = _wire(audit_record_typed(audit))
expect(audit_record_typed(audit_from_record(audit_wire).?).fields).to_equal(audit_wire.fields)
val publication = Publication(publication_id: "PUB-1", entity_type: "release", entity_id: "REL-1", provider_instance: "github", remote_id: "1", artifact_digest: "artifact", state: "verified")
val publication_wire = _wire(publication_record(publication))
expect(publication_record(publication_from_record(publication_wire).?).fields).to_equal(publication_wire.fields)
```

</details>

#### round trips release line candidate and immutable release fields

- round trips release line candidate and immutable release fields
   - Expected: release_line_record(release_line_from_record(line_wire).?).fields equals `line_wire.fields`
   - Expected: release_candidate_record(release_candidate_from_record(candidate_wire).?).fields equals `candidate_wire.fields`
   - Expected: release_record(release_from_record(release_wire).?).fields equals `release_wire.fields`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round trips release line candidate and immutable release fields")
val line = ReleaseLine(line_id: "simple/1.4", product: "simple", major: 1, minor: 4, source_ref: "release/1.4", support_state: "maintained", support_policy_digest: "support", remote_binding_ids: ["BIND-1"])
val line_wire = _wire(release_line_record(line))
expect(release_line_record(release_line_from_record(line_wire).?).fields).to_equal(line_wire.fields)
val candidate = ReleaseCandidate(candidate_id: "RC-1", version: "1.4.2", line_id: "simple/1.4", source_revision_id: "REV-1", gate_bundle_id: "BUNDLE-1", artifact_set_id: "ART-1", review_id: "REVIEW-1", state: "verified")
val candidate_wire = _wire(release_candidate_record(candidate))
expect(release_candidate_record(release_candidate_from_record(candidate_wire).?).fields).to_equal(candidate_wire.fields)
val release = ReleaseIdentity(release_id: "REL-1", version: "1.4.2", line_id: "simple/1.4", source_revision_id: "REV-1", source_tree_hash: "tree", git_commit_oid: "commit", git_tag_object_oid: "tag", gate_bundle_id: "BUNDLE-1", artifact_set_id: "ART-1", sbom_ids: ["SBOM-1"], provenance_ids: ["PROV-1", "PROV-2"], publication_ids: ["PUB-1"], state: "published", immutable: true)
val release_wire = _wire(release_record(release))
expect(release_record(release_from_record(release_wire).?).fields).to_equal(release_wire.fields)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-001`
- `REQ-007`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `41e1f990afa8c50adf92ba975b970bd4966c5c2cd4e6bfdd231824686fba6be7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `41e1f990afa8c50adf92ba975b970bd4966c5c2cd4e6bfdd231824686fba6be7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `41e1f990afa8c50adf92ba975b970bd4966c5c2cd4e6bfdd231824686fba6be7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/scv/lifecycle_entity_codec_spec.spl
mirror: doc/06_spec/01_unit/lib/scv/lifecycle_entity_codec_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/scv/lifecycle_entity_codec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/scv/lifecycle_entity_codec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/scv/lifecycle_entity_codec_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/scv/lifecycle_entity_codec_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round trips change and immutable revision fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_entity_codec_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round trips review finding approval and gate fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_entity_codec_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round trips work sync publication and audit fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
