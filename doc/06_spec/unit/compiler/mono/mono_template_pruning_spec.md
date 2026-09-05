# Consumed generic templates stop being emittable (plan section 9.3 step 12)

> Purpose: Prove that generic template pruning after monomorphization (plan 9.3 step 12).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Consumed generic templates stop being emittable (plan section 9.3 step 12)

Purpose: Prove that generic template pruning after monomorphization (plan 9.3 step 12).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mono/mono_template_pruning_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that generic template pruning after monomorphization (plan 9.3 step 12).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### generic template pruning after monomorphization (plan 9.3 step 12)

#### removes the template that has a specialization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- removes the template that has a specialization
- Verify: removes the template that has a specialization
   - Expected: count_named(result["mono_prune_test"], "box_it") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes the template that has a specialization")
step("Verify: removes the template that has a specialization")
# @req: REQ-COMPILER-MONO-001
val (result, _) = run_monomorphization(make_modules())
expect(count_named(result["mono_prune_test"], "box_it")).to_equal(0)
```

</details>

#### still emits the specialization

- still emits the specialization
- Verify: still emits the specialization
   - Expected: stats.specializations_created equals `1`
   - Expected: count_named(result["mono_prune_test"], "box_it$i64") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still emits the specialization")
step("Verify: still emits the specialization")
val (result, stats) = run_monomorphization(make_modules())
expect(stats.specializations_created).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(count_named(result["mono_prune_test"], "box_it$i64")).to_equal(1)
```

</details>

#### never drops a non-generic neighbour

- never drops a non-generic neighbour
- Verify: never drops a non-generic neighbour
   - Expected: count_named(out, "plain") equals `1`
   - Expected: count_named(out, "main") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never drops a non-generic neighbour")
step("Verify: never drops a non-generic neighbour")
val (result, _) = run_monomorphization(make_modules())
val out = result["mono_prune_test"]
expect(count_named(out, "plain")).to_equal(1)
expect(count_named(out, "main")).to_equal(1)
```

</details>

#### keeps a generic template that has zero instantiations

- keeps a generic template that has zero instantiations
- Verify: keeps a generic template that has zero instantiations
   - Expected: count_named(result["mono_prune_test"], "never_used") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a generic template that has zero instantiations")
step("Verify: keeps a generic template that has zero instantiations")
val (result, _) = run_monomorphization(make_modules())
expect(count_named(result["mono_prune_test"], "never_used")).to_equal(1)
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
- `REQ-COMPILER-MONO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `683e59a2f04a4995b426992384952f9bbc2cba5762121f0ae6065548b024e8f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `683e59a2f04a4995b426992384952f9bbc2cba5762121f0ae6065548b024e8f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `683e59a2f04a4995b426992384952f9bbc2cba5762121f0ae6065548b024e8f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/mono/mono_template_pruning_spec.spl
mirror: doc/06_spec/unit/compiler/mono/mono_template_pruning_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mono/mono_template_pruning_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mono/mono_template_pruning_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mono/mono_template_pruning_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/mono/mono_template_pruning_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes the template that has a specialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mono/mono_template_pruning_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still emits the specialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mono/mono_template_pruning_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never drops a non-generic neighbour' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
