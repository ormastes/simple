# integration_policy_evidence_spec

> Protected integration binds canonical policy and every required manifest gate to retained evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# integration_policy_evidence_spec

Protected integration binds canonical policy and every required manifest gate to retained evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/integration_policy_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Protected integration binds canonical policy and every required manifest gate to retained evidence.

## Scenarios

### SJ canonical policy and gate evidence binding

#### rejects a complete bundle whose passing run is unrelated to the required manifest gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a complete bundle whose passing run is unrelated to the required manifest gate
   - Expected: plan_integration_with_policy(request, [approval], [unrelated], bundle, payload, manifest).code equals `SJ_GATE_EVIDENCE_MISSING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a complete bundle whose passing run is unrelated to the required manifest gate")
val payload = canonical_policy_fixture()
val policy = parse_canonical_lifecycle_vcs_policy(payload)
val approval = Approval(approval_id: "APR-1", review_id: "REVIEW-1", revision_id: "REV-1", tree_digest: "tree", reviewer: "reviewer", authority: "maintainer", policy_digest: policy.digest, evidence_bundle_digest: "evidence", created_at: "time", state: "approved")
val unrelated = GateRun(gate_run_id: "RUN-1", revision_id: "REV-1", gate_id: "unrelated", policy_digest: policy.digest, tool_digest: "tool", environment_digest: "env", verdict: "pass", evidence_objects: ["log"])
val bundle = GateBundle(gate_bundle_id: "BUNDLE-1", revision_id: "REV-1", gate_run_ids: ["RUN-1"], approval_ids: ["APR-1"], complete: true, bundle_digest: "bundle", policy_digest: policy.digest)
val request = IntegrateRequest(change_id: "CHG-1", revision_id: "REV-1", base_revision_id: "REV-0", expected_remote_revision: "GIT-1", observed_remote_revision: "GIT-1", target_ref: "integration/main", policy_digest: policy.digest, gate_profile: "standard", actor: "agent", authority: "maintainer", dry_run: true)
val required = GateManifestEntry(gate_id: "conflict-tree", tier: "push", push_blocking: true, mode: "ref", command: "check-conflict-tree", description: "required")
val manifest = plan_protected_gate_manifest([required], "REV-0", "REV-1")
expect(plan_integration_with_policy(request, [approval], [unrelated], bundle, payload, manifest).code).to_equal("SJ_GATE_EVIDENCE_MISSING")
```

</details>

#### rejects a policy payload missing canonical authoring and break-glass clauses

- rejects a policy payload missing canonical authoring and break-glass clauses
   - Expected: parse_canonical_lifecycle_vcs_policy(payload).error equals `required break-glass clause is missing: audit: required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a policy payload missing canonical authoring and break-glass clauses")
val payload = canonical_policy_fixture().replace("      audit: required\n", "")
expect(parse_canonical_lifecycle_vcs_policy(payload).error).to_equal("required break-glass clause is missing: audit: required")
```

</details>

#### does not accept authoring clauses nested under an unrelated section

- does not accept authoring clauses nested under an unrelated section
   - Expected: parse_canonical_lifecycle_vcs_policy(payload).error equals `required authoring clause is missing: jj_workspace: preferred`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not accept authoring clauses nested under an unrelated section")
val payload = canonical_policy_fixture().replace("  authoring:\n", "  other:\n")
expect(parse_canonical_lifecycle_vcs_policy(payload).error).to_equal("required authoring clause is missing: jj_workspace: preferred")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-002`
- `REQ-003`
- `REQ-008`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc42999d32494d4c58b468fd5ab9e04277a10c72f4485418632484f49ca3f10a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc42999d32494d4c58b468fd5ab9e04277a10c72f4485418632484f49ca3f10a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc42999d32494d4c58b468fd5ab9e04277a10c72f4485418632484f49ca3f10a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/sj/integration_policy_evidence_spec.spl
mirror: doc/06_spec/01_unit/app/sj/integration_policy_evidence_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/sj/integration_policy_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/sj/integration_policy_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/sj/integration_policy_evidence_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/sj/integration_policy_evidence_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a complete bundle whose passing run is unrelated to the required manifest gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sj/integration_policy_evidence_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a policy payload missing canonical authoring and break-glass clauses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sj/integration_policy_evidence_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not accept authoring clauses nested under an unrelated section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
