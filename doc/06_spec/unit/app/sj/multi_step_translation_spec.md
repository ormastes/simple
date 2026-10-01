# Multi-Step Translation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-Step Translation Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/sj/multi_step_translation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Multi-Step Translation - Commit

#### translates git commit -m to describe + new

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- translates git commit -m to describe + new
   - Expected: plan.classification equals `multi_step`
   - Expected: plan.commands.len() equals `2i64`
   - Expected: plan.commands[1i64] equals `jj new`
   - Expected: plan.lease_kind equals `LEASE_EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git commit -m to describe + new")
val plan = translate(["git", "commit", "-m", "my message"])
expect(plan.classification).to_equal("multi_step")
expect(plan.commands.len()).to_equal(2i64)
expect(plan.commands[0i64]).to_contain("jj describe")
expect(plan.commands[1i64]).to_equal("jj new")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

#### translates git commit --amend to describe

- translates git commit --amend to describe
   - Expected: plan.classification equals `direct_jj`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git commit --amend to describe")
val plan = translate(["git", "commit", "--amend"])
expect(plan.classification).to_equal("direct_jj")
expect(plan.commands[0i64]).to_contain("jj describe")
```

</details>

### Multi-Step Translation - Checkout -b

#### translates git checkout -b to new + bookmark create

- translates git checkout -b to new + bookmark create
   - Expected: plan.classification equals `multi_step`
   - Expected: plan.commands.len() equals `2i64`
   - Expected: plan.commands[0i64] equals `jj new`
   - Expected: plan.lease_kind equals `LEASE_EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git checkout -b to new + bookmark create")
val plan = translate(["git", "checkout", "-b", "feature-x"])
expect(plan.classification).to_equal("multi_step")
expect(plan.commands.len()).to_equal(2i64)
expect(plan.commands[0i64]).to_equal("jj new")
expect(plan.commands[1i64]).to_contain("bookmark create feature-x")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

#### translates git checkout -b with base to new <base> + bookmark

- translates git checkout -b with base to new <base> + bookmark
   - Expected: plan.commands[0i64] equals `jj new main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git checkout -b with base to new <base> + bookmark")
val plan = translate(["git", "checkout", "-b", "feature-y", "main"])
expect(plan.commands[0i64]).to_equal("jj new main")
expect(plan.commands[1i64]).to_contain("bookmark create feature-y")
```

</details>

### Multi-Step Translation - Pull

#### translates git pull to fetch + rebase

- translates git pull to fetch + rebase
   - Expected: plan.classification equals `multi_step`
   - Expected: plan.commands.len() equals `2i64`
   - Expected: plan.commands[0i64] equals `jj git fetch`
   - Expected: plan.commands[1i64] equals `jj rebase -d main@origin`
   - Expected: plan.lease_kind equals `LEASE_EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git pull to fetch + rebase")
val plan = translate(["git", "pull"])
expect(plan.classification).to_equal("multi_step")
expect(plan.commands.len()).to_equal(2i64)
expect(plan.commands[0i64]).to_equal("jj git fetch")
expect(plan.commands[1i64]).to_equal("jj rebase -d main@origin")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

### Multi-Step Translation - Lease Sharing

#### all multi-step commands use exclusive leases

- all multi-step commands use exclusive leases
   - Expected: commit_plan.lease_kind equals `LEASE_EXCLUSIVE`
   - Expected: pull_plan.lease_kind equals `LEASE_EXCLUSIVE`
   - Expected: branch_plan.lease_kind equals `LEASE_EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all multi-step commands use exclusive leases")
val commit_plan = translate(["git", "commit", "-m", "x"])
val pull_plan = translate(["git", "pull"])
val branch_plan = translate(["git", "checkout", "-b", "test"])
expect(commit_plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
expect(pull_plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
expect(branch_plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `02c2dfc9d41e58e8b57dc4a12fb2b4fbe12c9807eacd43551300de8a34e3bd0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02c2dfc9d41e58e8b57dc4a12fb2b4fbe12c9807eacd43551300de8a34e3bd0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02c2dfc9d41e58e8b57dc4a12fb2b4fbe12c9807eacd43551300de8a34e3bd0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sj/multi_step_translation_spec.spl
mirror: doc/06_spec/unit/app/sj/multi_step_translation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sj/multi_step_translation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sj/multi_step_translation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sj/multi_step_translation_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates git commit -m to describe + new' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/multi_step_translation_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates git commit --amend to describe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/multi_step_translation_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates git checkout -b to new + bookmark create' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
