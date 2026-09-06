# Submodule Policy Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Submodule Policy Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/sj/submodule_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#
#
#
#
#

## Scenarios

### Submodule Policy - Detection

#### detects git submodule add

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects git submodule add
   - Expected: plan.is_submodule is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects git submodule add")
val plan = classify_submodule(["git", "submodule", "add", "https://example.com/repo", "vendor/lib"])
expect(plan.is_submodule).to_equal(true)
```

</details>

#### detects git submodule status

- detects git submodule status
   - Expected: plan.is_submodule is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects git submodule status")
val plan = classify_submodule(["git", "submodule", "status"])
expect(plan.is_submodule).to_equal(true)
```

</details>

#### does not flag non-submodule git commands

- does not flag non-submodule git commands
   - Expected: plan.is_submodule is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag non-submodule git commands")
val plan = classify_submodule(["git", "status"])
expect(plan.is_submodule).to_equal(false)
```

</details>

#### does not flag non-git commands

- does not flag non-git commands
   - Expected: plan.is_submodule is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag non-git commands")
val plan = classify_submodule(["describe", "-m", "test"])
expect(plan.is_submodule).to_equal(false)
```

</details>

### Submodule Policy - Exclusive Lease

#### submodule add uses exclusive lease

- submodule add uses exclusive lease
   - Expected: plan.lease_kind equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submodule add uses exclusive lease")
val plan = classify_submodule(["git", "submodule", "add", "url", "path"])
expect(plan.lease_kind).to_equal(0i64)
```

</details>

#### submodule status uses shared lease

- submodule status uses shared lease
   - Expected: plan.lease_kind equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submodule status uses shared lease")
val plan = classify_submodule(["git", "submodule", "status"])
expect(plan.lease_kind).to_equal(1i64)
```

</details>

#### submodule update uses exclusive lease

- submodule update uses exclusive lease
   - Expected: plan.lease_kind equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submodule update uses exclusive lease")
# NOTE: the shipped code has no dedicated `update` branch — this reaches
# the exclusive-lease fallback. The removed shim DID have a dedicated
# `update` branch; it returned the same value, so this example agreed
# with shipped behaviour by coincidence rather than by coverage.
val plan = classify_submodule(["git", "submodule", "update"])
expect(plan.lease_kind).to_equal(0i64)
```

</details>

### Submodule Policy - Warning

#### submodule add produces WARN

- submodule add produces WARN


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submodule add produces WARN")
val plan = classify_submodule(["git", "submodule", "add", "url", "vendor/lib"])
expect(plan.warning).to_contain("WARN[SUBMODULE]")
expect(plan.warning).to_contain("gitlink")
```

</details>

#### submodule status has no warning

- submodule status has no warning
   - Expected: plan.warning equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submodule status has no warning")
val plan = classify_submodule(["git", "submodule", "status"])
expect(plan.warning).to_equal("")
```

</details>

### Submodule Policy - Auto-Pin

#### submodule add produces auto-pin command

- submodule add produces auto-pin command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submodule add produces auto-pin command")
val plan = classify_submodule(["git", "submodule", "add", "url", "vendor/lib"])
expect(plan.auto_pin_cmd).to_contain("git commit")
expect(plan.auto_pin_cmd).to_contain("pin submodule vendor/lib")
```

</details>

#### submodule status has no auto-pin

- submodule status has no auto-pin
   - Expected: plan.auto_pin_cmd equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submodule status has no auto-pin")
val plan = classify_submodule(["git", "submodule", "status"])
expect(plan.auto_pin_cmd).to_equal("")
```

</details>

### Submodule Policy - Read Negative

#### short argv returns non-submodule

- short argv returns non-submodule
   - Expected: plan.is_submodule is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("short argv returns non-submodule")
val plan = classify_submodule(["git"])
expect(plan.is_submodule).to_equal(false)
```

</details>

#### empty argv returns non-submodule

- empty argv returns non-submodule
   - Expected: plan.is_submodule is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty argv returns non-submodule")
val plan = classify_submodule([])
expect(plan.is_submodule).to_equal(false)
```

</details>

### Submodule Policy - drift pins

#### a non-submodule plan carries the EXCLUSIVE lease, not the shared one

- a non-submodule plan carries the EXCLUSIVE lease, not the shared one
   - Expected: classify_submodule(["git", "status"]).lease_kind equals `0i64`
   - Expected: classify_submodule([]).lease_kind equals `0i64`
   - Expected: classify_submodule(["describe", "-m", "x"]).lease_kind equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a non-submodule plan carries the EXCLUSIVE lease, not the shared one")
# DRIFT 1. The removed shim returned LEASE_SHARED (1) from both
# non-submodule early returns; the shipped code returns LEASE_EXCLUSIVE
# (0) via `submodule_plan_none()`. The shim never asserted lease_kind on
# a non-submodule plan, so the divergence was invisible in both
# directions. This pins the shipped value.
expect(classify_submodule(["git", "status"]).lease_kind).to_equal(0i64)
expect(classify_submodule([]).lease_kind).to_equal(0i64)
expect(classify_submodule(["describe", "-m", "x"]).lease_kind).to_equal(0i64)
```

</details>

#### a two-argument submodule add uses argv[3] as the pinned path

- a two-argument submodule add uses argv[3] as the pinned path
   - Expected: plan.is_submodule is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a two-argument submodule add uses argv[3] as the pinned path")
# DRIFT 2, and it is a live divergence inside shipped code, not just in
# the removed shim. `src/app/sj_daemon/submodule_policy.spl` falls back
# argv[4] -> argv[3] -> "submodule"; `src/app/sj/policy.spl` falls back
# argv[4] -> "submodule" only, losing the argv[3] step. The daemon
# definition wins here, so this asserts "vendor/lib". If policy.spl's
# copy ever became the one that resolves, this example goes red — which
# is the point.
val plan = classify_submodule(["git", "submodule", "add", "vendor/lib"])
expect(plan.is_submodule).to_equal(true)
expect(plan.auto_pin_cmd).to_contain("pin submodule vendor/lib")
```

</details>

#### a bare submodule add with no path falls back to the literal 'submodule'

- a bare submodule add with no path falls back to the literal 'submodule'
   - Expected: plan.is_submodule is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bare submodule add with no path falls back to the literal 'submodule'")
val plan = classify_submodule(["git", "submodule", "add"])
expect(plan.is_submodule).to_equal(true)
expect(plan.auto_pin_cmd).to_contain("pin submodule submodule")
```

</details>

#### the auto-pin command is a --no-verify commit

- the auto-pin command is a --no-verify commit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the auto-pin command is a --no-verify commit")
val plan = classify_submodule(["git", "submodule", "add", "url", "vendor/lib"])
expect(plan.auto_pin_cmd).to_start_with("git commit --no-verify -m ")
```

</details>

#### an unrecognised submodule verb is a submodule with an exclusive lease and no warning

- an unrecognised submodule verb is a submodule with an exclusive lease and no warning
   - Expected: plan.is_submodule is true
   - Expected: plan.lease_kind equals `0i64`
   - Expected: plan.warning equals ``
   - Expected: plan.auto_pin_cmd equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unrecognised submodule verb is a submodule with an exclusive lease and no warning")
val plan = classify_submodule(["git", "submodule", "deinit", "vendor/lib"])
expect(plan.is_submodule).to_equal(true)
expect(plan.lease_kind).to_equal(0i64)
expect(plan.warning).to_equal("")
expect(plan.auto_pin_cmd).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `9cfd374283f019ba420028dafbce9fee513820c6cd81641b137ad191f3e6692e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9cfd374283f019ba420028dafbce9fee513820c6cd81641b137ad191f3e6692e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9cfd374283f019ba420028dafbce9fee513820c6cd81641b137ad191f3e6692e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sj/submodule_policy_spec.spl
mirror: doc/06_spec/unit/app/sj/submodule_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sj/submodule_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sj/submodule_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sj/submodule_policy_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects git submodule add' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/submodule_policy_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects git submodule status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/submodule_policy_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag non-submodule git commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
