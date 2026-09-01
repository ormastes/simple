# gate_manifest_spec

> Every protected integration plans all manifest-marked push gates against pinned revisions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gate_manifest_spec

Every protected integration plans all manifest-marked push gates against pinned revisions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/gate_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Every protected integration plans all manifest-marked push gates against pinned revisions.

## Scenarios

### SJ protected gate manifest planning

#### plans every push-blocking row against exact BASE and HEAD

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans every push-blocking row against exact BASE and HEAD
- Load the authoritative gate manifest
- Bind each protected gate to pinned revisions
   - Expected: plan.invocations.len() equals `2`
   - Expected: plan.invocations[0].args equals `["base-oid..head-oid"]`
   - Expected: plan.invocations[1].args equals `["head-oid"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("plans every push-blocking row against exact BASE and HEAD")
step("Load the authoritative gate manifest")
val entries = parse_gate_manifest(gate_fixture())
step("Bind each protected gate to pinned revisions")
val plan = plan_protected_gate_manifest(entries, "base-oid", "head-oid")
expect(plan.valid).to_be(true)
expect(plan.invocations.len()).to_equal(2)
expect(plan.invocations[0].args).to_equal(["base-oid..head-oid"])
expect(plan.invocations[1].args).to_equal(["head-oid"])
```

</details>

#### fails closed on empty or unsupported protected scope

- fails closed on empty or unsupported protected scope
   - Expected: plan_protected_gate_manifest([], "base", "head").error equals `protected gate manifest selected zero push-blocking gates`
   - Expected: plan_protected_gate_manifest(parse_gate_manifest(unsupported), "base", "head").error equals `unsupported protected gate mode: receipt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed on empty or unsupported protected scope")
expect(plan_protected_gate_manifest([], "base", "head").error).to_equal("protected gate manifest selected zero push-blocking gates")
val unsupported = gate_fixture().replace("range", "receipt")
expect(plan_protected_gate_manifest(parse_gate_manifest(unsupported), "base", "head").error).to_equal("unsupported protected gate mode: receipt")
```

</details>

#### rejects duplicate blocking gate identities

- rejects duplicate blocking gate identities
   - Expected: plan_protected_gate_manifest([entry, entry], "base", "head").error equals `duplicate push-blocking gate identity: push-one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects duplicate blocking gate identities")
val entry = GateManifestEntry(gate_id: "push-one", tier: "push", push_blocking: true, mode: "ref", command: "check-one", description: "one")
expect(plan_protected_gate_manifest([entry, entry], "base", "head").error).to_equal("duplicate push-blocking gate identity: push-one")
```

</details>

#### does not silently omit a malformed mandatory row

- does not silently omit a malformed mandatory row
   - Expected: plan_protected_gate_manifest(parse_gate_manifest(malformed), "base", "head").error equals `push-blocking gate has no identity or command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not silently omit a malformed mandatory row")
val malformed = gate_fixture() + "    broken, push, true\n"
expect(plan_protected_gate_manifest(parse_gate_manifest(malformed), "base", "head").error).to_equal("push-blocking gate has no identity or command")
```

</details>

#### preserves commas inside quoted commands and descriptions

- preserves commas inside quoted commands and descriptions
   - Expected: entries.len() equals `1`
   - Expected: entries[0].command equals `sh check.shs --values a,b`
   - Expected: entries[0].description equals `checks a,b together`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves commas inside quoted commands and descriptions")
val payload = "must_check_gates |id, tier, push_blocking, mode, command, description|\n    quoted, push, true, ref, \"sh check.shs --values a,b\", \"checks a,b together\"\n"
val entries = parse_gate_manifest(payload)
expect(entries.len()).to_equal(1)
expect(entries[0].command).to_equal("sh check.shs --values a,b")
expect(entries[0].description).to_equal("checks a,b together")
```

</details>

#### rejects tier and boolean typos instead of disabling a required gate

- rejects tier and boolean typos instead of disabling a required gate
   - Expected: plan_protected_gate_manifest(parse_gate_manifest(bad_bool), "base", "head").error equals `push-blocking gate has no identity or command`
   - Expected: plan_protected_gate_manifest(parse_gate_manifest(bad_tier), "base", "head").error equals `push-blocking gate has no identity or command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects tier and boolean typos instead of disabling a required gate")
val bad_bool = gate_fixture().replace("push, true", "push, tru")
expect(plan_protected_gate_manifest(parse_gate_manifest(bad_bool), "base", "head").error).to_equal("push-blocking gate has no identity or command")
val bad_tier = gate_fixture().replace("conflicts, push", "conflicts, puch")
expect(plan_protected_gate_manifest(parse_gate_manifest(bad_tier), "base", "head").error).to_equal("push-blocking gate has no identity or command")
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

- `REQ-SSPEC-UNIT`
- `REQ-002`
- `REQ-008`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `707dfa2d36ffc16319bdc4634aea87d2eb292f3e33fc953377f89371a3dfd406`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `707dfa2d36ffc16319bdc4634aea87d2eb292f3e33fc953377f89371a3dfd406`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `707dfa2d36ffc16319bdc4634aea87d2eb292f3e33fc953377f89371a3dfd406`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/sj/gate_manifest_spec.spl
mirror: doc/06_spec/01_unit/app/sj/gate_manifest_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/sj/gate_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/sj/gate_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/sj/gate_manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/sj/gate_manifest_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/sj/gate_manifest_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans every push-blocking row against exact BASE and HEAD' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sj/gate_manifest_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on empty or unsupported protected scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sj/gate_manifest_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects duplicate blocking gate identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
