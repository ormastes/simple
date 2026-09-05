# lifecycle_audit_routing_spec

> Lifecycle operations are audit-bound and review escalation is bounded.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_audit_routing_spec

Lifecycle operations are audit-bound and review escalation is bounded.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/scv/lifecycle_audit_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Lifecycle operations are audit-bound and review escalation is bounded.

## Scenarios

### Lifecycle audit and bounded review routing

#### binds a protected operation to actor, policy, input, and output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds a protected operation to actor, policy, input, and output


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds a protected operation to actor, policy, input, and output")
val audit = lifecycle_operation_audit(OperationAuditInput(operation_kind: "integrate", entity_id: "chg_1", actor_id: "agent", authority: "maintainer", policy_digest: "policy-1", input_digest: "input-1", output_digest: "output-1", state: "planned"))
expect(audit.operation_id).to_start_with("op_")
expect(lifecycle_record_decode(lifecycle_record_encode(lifecycle_operation_record(audit))).ok).to_be(true)
```

</details>

#### admits one concrete evidence-driven escalation

- admits one concrete evidence-driven escalation
- Name the unresolved question and missing evidence
   - Expected: review_escalation_admit(standard_route(), request).status equals `model_escalation_admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits one concrete evidence-driven escalation")
step("Name the unresolved question and missing evidence")
val request = ReviewEscalationRequest(parent_run_id: "RUN-1", reviewer: "fast-reviewer", depth: 1, existing_child_count: 0, question: "Can the CAS race with a refreshed workspace?", prior_question_fingerprints: [], severity: "high", missing_evidence: "concurrent transaction trace")
expect(review_escalation_admit(standard_route(), request).status).to_equal("model_escalation_admitted")
```

</details>

#### rejects cycles and routes terminal critical questions to a human

- rejects cycles and routes terminal critical questions to a human
   - Expected: review_escalation_admit(standard_route(), cycle).code equals `REVIEW_ESCALATION_CYCLE`
   - Expected: review_escalation_admit(standard_route(), terminal).status equals `human_required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects cycles and routes terminal critical questions to a human")
val question = "Can lease ordering deadlock?"
val cycle = ReviewEscalationRequest(parent_run_id: "RUN-2", reviewer: "strong-reviewer", depth: 2, existing_child_count: 1, question: question, prior_question_fingerprints: [review_question_fingerprint(question)], severity: "high", missing_evidence: "lock-order model")
expect(review_escalation_admit(standard_route(), cycle).code).to_equal("REVIEW_ESCALATION_CYCLE")
val terminal = ReviewEscalationRequest(parent_run_id: "RUN-3", reviewer: "specialist", depth: 3, existing_child_count: 0, question: "Is release identity ambiguous?", prior_question_fingerprints: [], severity: "critical", missing_evidence: "independent signature verification")
expect(review_escalation_admit(standard_route(), terminal).status).to_equal("human_required")
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
- `REQ-003`
- `REQ-008`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82f9f7655b909e68c0e890fe5e491a620c9c0db4ff03b08dfc908db01b802688`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82f9f7655b909e68c0e890fe5e491a620c9c0db4ff03b08dfc908db01b802688`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82f9f7655b909e68c0e890fe5e491a620c9c0db4ff03b08dfc908db01b802688`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/scv/lifecycle_audit_routing_spec.spl
mirror: doc/06_spec/01_unit/lib/scv/lifecycle_audit_routing_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/scv/lifecycle_audit_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/scv/lifecycle_audit_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/scv/lifecycle_audit_routing_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/scv/lifecycle_audit_routing_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds a protected operation to actor, policy, input, and output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_audit_routing_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits one concrete evidence-driven escalation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_audit_routing_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects cycles and routes terminal critical questions to a human' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
