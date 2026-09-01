# Direct JJ Translation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direct JJ Translation Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/sj/direct_jj_translation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Direct JJ Translation - Read Verbs

#### translates git status to jj status

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- translates git status to jj status
   - Expected: plan.commands[0i64] equals `jj status`
   - Expected: plan.lease_kind equals `LEASE_SHARED`
   - Expected: plan.classification equals `direct_jj`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git status to jj status")
val plan = translate(["git", "status"])
expect(plan.commands[0i64]).to_equal("jj status")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
expect(plan.classification).to_equal("direct_jj")
```

</details>

#### translates git log to jj log

- translates git log to jj log
   - Expected: plan.commands[0i64] equals `jj log`
   - Expected: plan.lease_kind equals `LEASE_SHARED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git log to jj log")
val plan = translate(["git", "log"])
expect(plan.commands[0i64]).to_equal("jj log")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### translates git diff to jj diff

- translates git diff to jj diff
   - Expected: plan.commands[0i64] equals `jj diff`
   - Expected: plan.lease_kind equals `LEASE_SHARED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git diff to jj diff")
val plan = translate(["git", "diff"])
expect(plan.commands[0i64]).to_equal("jj diff")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### translates git blame to jj file annotate

- translates git blame to jj file annotate
   - Expected: plan.commands[0i64] equals `jj file annotate src/main.spl`
   - Expected: plan.lease_kind equals `LEASE_SHARED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git blame to jj file annotate")
val plan = translate(["git", "blame", "src/main.spl"])
expect(plan.commands[0i64]).to_equal("jj file annotate src/main.spl")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### translates git branch --list to jj bookmark list

- translates git branch --list to jj bookmark list
   - Expected: plan.commands[0i64] equals `jj bookmark list`
   - Expected: plan.lease_kind equals `LEASE_SHARED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git branch --list to jj bookmark list")
val plan = translate(["git", "branch", "--list"])
expect(plan.commands[0i64]).to_equal("jj bookmark list")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

### Direct JJ Translation - Mutating Verbs

#### translates git checkout <rev> to jj new <rev>

- translates git checkout <rev> to jj new <rev>
   - Expected: plan.commands[0i64] equals `jj new abc123`
   - Expected: plan.lease_kind equals `LEASE_EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates git checkout <rev> to jj new <rev>")
val plan = translate(["git", "checkout", "abc123"])
expect(plan.commands[0i64]).to_equal("jj new abc123")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

#### passes through jj-native verbs with exclusive lease

- passes through jj-native verbs with exclusive lease
   - Expected: plan.commands[0i64] equals `jj describe -m test message`
   - Expected: plan.lease_kind equals `LEASE_EXCLUSIVE`
   - Expected: plan.classification equals `direct_jj`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through jj-native verbs with exclusive lease")
val plan = translate(["describe", "-m", "test message"])
expect(plan.commands[0i64]).to_equal("jj describe -m test message")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
expect(plan.classification).to_equal("direct_jj")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `5f700c5d7e532924731a06ab89c46758d8351153c1213dfe8a44e3d4cb171972`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f700c5d7e532924731a06ab89c46758d8351153c1213dfe8a44e3d4cb171972`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f700c5d7e532924731a06ab89c46758d8351153c1213dfe8a44e3d4cb171972`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sj/direct_jj_translation_spec.spl
mirror: doc/06_spec/unit/app/sj/direct_jj_translation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sj/direct_jj_translation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sj/direct_jj_translation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sj/direct_jj_translation_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates git status to jj status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/direct_jj_translation_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates git log to jj log' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/direct_jj_translation_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates git diff to jj diff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
