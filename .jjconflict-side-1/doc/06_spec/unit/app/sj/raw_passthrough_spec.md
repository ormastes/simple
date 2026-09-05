# Raw Passthrough Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Raw Passthrough Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/sj/raw_passthrough_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Raw Passthrough - sj raw jj

#### passes through raw jj commands with shared lease

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes through raw jj commands with shared lease
   - Expected: plan.classification equals `raw_passthrough`
   - Expected: plan.commands[0i64] equals `jj op log`
   - Expected: plan.lease_kind equals `LEASE_SHARED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through raw jj commands with shared lease")
val plan = translate(["raw", "jj", "op", "log"])
expect(plan.classification).to_equal("raw_passthrough")
expect(plan.commands[0i64]).to_equal("jj op log")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

#### passes through raw git commands with exclusive lease

- passes through raw git commands with exclusive lease
   - Expected: plan.classification equals `raw_passthrough`
   - Expected: plan.commands[0i64] equals `git gc`
   - Expected: plan.lease_kind equals `LEASE_EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through raw git commands with exclusive lease")
val plan = translate(["raw", "git", "gc"])
expect(plan.classification).to_equal("raw_passthrough")
expect(plan.commands[0i64]).to_equal("git gc")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
```

</details>

### Raw Passthrough - LFS

#### routes git lfs as raw passthrough with shared lease

- routes git lfs as raw passthrough with shared lease
   - Expected: plan.classification equals `raw_passthrough`
   - Expected: plan.commands[0i64] equals `git lfs pull`
   - Expected: plan.lease_kind equals `LEASE_SHARED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes git lfs as raw passthrough with shared lease")
val plan = translate(["git", "lfs", "pull"])
expect(plan.classification).to_equal("raw_passthrough")
expect(plan.commands[0i64]).to_equal("git lfs pull")
expect(plan.lease_kind).to_equal(LEASE_SHARED)
```

</details>

### Raw Passthrough - Clean

#### routes git clean as raw passthrough with warning

- routes git clean as raw passthrough with warning
   - Expected: plan.classification equals `raw_passthrough`
   - Expected: plan.commands[0i64] equals `git clean -fd`
   - Expected: plan.lease_kind equals `LEASE_EXCLUSIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes git clean as raw passthrough with warning")
val plan = translate(["git", "clean", "-fd"])
expect(plan.classification).to_equal("raw_passthrough")
expect(plan.commands[0i64]).to_equal("git clean -fd")
expect(plan.lease_kind).to_equal(LEASE_EXCLUSIVE)
expect(plan.warning).to_contain("WARN")
```

</details>

### Raw Passthrough - Unknown Verb

#### treats unknown git verbs as direct jj commands

- treats unknown git verbs as direct jj commands
   - Expected: plan.classification equals `direct_jj`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats unknown git verbs as direct jj commands")
val plan = translate(["git", "unknown-verb", "arg1"])
expect(plan.classification).to_equal("direct_jj")
expect(plan.commands[0i64]).to_contain("jj")
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e8e464bd97704bc496352e76e536ebe7e6a43873d49043a91b042044e8bf9e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e8e464bd97704bc496352e76e536ebe7e6a43873d49043a91b042044e8bf9e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e8e464bd97704bc496352e76e536ebe7e6a43873d49043a91b042044e8bf9e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sj/raw_passthrough_spec.spl
mirror: doc/06_spec/unit/app/sj/raw_passthrough_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sj/raw_passthrough_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sj/raw_passthrough_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sj/raw_passthrough_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes through raw jj commands with shared lease' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/raw_passthrough_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes through raw git commands with exclusive lease' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/raw_passthrough_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes git lfs as raw passthrough with shared lease' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
