# lifecycle_policy_plan_spec

> Typed SJ policy and operation planning fail closed before backend mutation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_policy_plan_spec

Typed SJ policy and operation planning fail closed before backend mutation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/lifecycle_policy_plan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Typed SJ policy and operation planning fail closed before backend mutation.

## Scenarios

### Typed SJ lifecycle policy

#### recognizes typed integration without executing it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes typed integration without executing it
   - Expected: legacy_argv_operation(["git", "push"]).kind equals `SJ_OP_INTEGRATE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recognizes typed integration without executing it")
val operation = vcs_operation(SJ_OP_INTEGRATE, "chg_1", "integration/main", true)
expect(vcs_operation_valid(operation)).to_be(true)
expect(operation.dry_run).to_be(true)
expect(legacy_argv_operation(["git", "push"]).kind).to_equal(SJ_OP_INTEGRATE)
expect(legacy_argv_operation(["git", "push"]).dry_run).to_be(true)
```

</details>

#### rejects missing server-side enforcement evidence

- rejects missing server-side enforcement evidence
- Parse an incomplete protected-ref policy
   - Expected: parse_lifecycle_vcs_policy(payload).error equals `protected ref does not require independent server enforcement`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects missing server-side enforcement evidence")
step("Parse an incomplete protected-ref policy")
val payload = "policy:\n  schema: spipe-vcs/2\n  protected_refs:\n    - ref: main\n      mutator: sj.integrate\n      update: fast_forward\n      force: deny\n      required_profile: standard\n      server_enforcement_required: false\n"
expect(parse_lifecycle_vcs_policy(payload).error).to_equal("protected ref does not require independent server enforcement")
```

</details>

#### rejects duplicate protected-ref declarations

- rejects duplicate protected-ref declarations
   - Expected: parse_lifecycle_vcs_policy(payload).error equals `protected ref policy is contradictory or duplicated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects duplicate protected-ref declarations")
val row = "    - ref: main\n      mutator: sj.integrate\n      update: fast_forward\n      force: deny\n      required_profile: standard\n      server_enforcement_required: true\n"
val payload = "policy:\n  schema: spipe-vcs/2\n  protected_refs:\n" + row + row
expect(parse_lifecycle_vcs_policy(payload).error).to_equal("protected ref policy is contradictory or duplicated")
```

</details>

#### resolves release tag prefix wildcards exactly

- resolves release tag prefix wildcards exactly
   - Expected: lifecycle_policy_ref(policy, "refs/tags/v1.4.2").?.mutator equals `sj.create_release_tag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resolves release tag prefix wildcards exactly")
val row = "    - ref_pattern: refs/tags/v*\n      mutator: sj.create_release_tag\n      update: immutable_annotated_signed\n      force: deny\n      required_profile: release\n      server_enforcement_required: true\n"
val policy = parse_lifecycle_vcs_policy("policy:\n  schema: spipe-vcs/2\n  protected_refs:\n" + row)
expect(policy.valid).to_be(true)
expect(lifecycle_policy_ref(policy, "refs/tags/v1.4.2").?.mutator).to_equal("sj.create_release_tag")
expect(lifecycle_policy_ref(policy, "refs/heads/v1.4.2")).to_be_nil()
```

</details>

#### does not promote a partial parser result into canonical policy

- does not promote a partial parser result into canonical policy
   - Expected: parse_canonical_lifecycle_vcs_policy(payload).error equals `required protected ref class is missing: integration/main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not promote a partial parser result into canonical policy")
val row = "    - ref: main\n      mutator: sj.integrate\n      update: fast_forward_or_merge_queue\n      force: deny\n      required_profile: standard\n      server_enforcement_required: true\n"
val payload = "policy:\n  schema: spipe-vcs/2\n  protected_refs:\n" + row
expect(parse_lifecycle_vcs_policy(payload).valid).to_be(true)
expect(parse_canonical_lifecycle_vcs_policy(payload).error).to_equal("required protected ref class is missing: integration/main")
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
- `REQ-002`
- `REQ-008`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d52fbc0764c9e421325e90348fe3baf3421a2939a3490d37322ec274ab72b457`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d52fbc0764c9e421325e90348fe3baf3421a2939a3490d37322ec274ab72b457`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d52fbc0764c9e421325e90348fe3baf3421a2939a3490d37322ec274ab72b457`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/sj/lifecycle_policy_plan_spec.spl
mirror: doc/06_spec/01_unit/app/sj/lifecycle_policy_plan_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/sj/lifecycle_policy_plan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/sj/lifecycle_policy_plan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/sj/lifecycle_policy_plan_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/sj/lifecycle_policy_plan_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes typed integration without executing it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sj/lifecycle_policy_plan_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing server-side enforcement evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sj/lifecycle_policy_plan_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects duplicate protected-ref declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
