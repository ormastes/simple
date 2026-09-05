# effect_verifier_spec

> Purpose: Prove that effect verifier.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# effect_verifier_spec

Purpose: Prove that effect verifier.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/effect_verifier_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that effect verifier.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### effect verifier

### @copy_budget — accepted

#### accepts copies that fit the budget

- accepts copies that fit the budget
- Verify: accepts copies that fit the budget
   - Expected: v.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts copies that fit the budget")
step("Verify: accepts copies that fit the budget")
# @req: REQ-COMPILER-SEMANTICS-001
val v = check_copy_budget("blit_row", 64, [copy("Rect", 16), copy("Color", 4)], 0)
expect(v.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### accepts a zero-budget function that copies nothing

- accepts a zero-budget function that copies nothing
- Verify: accepts a zero-budget function that copies nothing
   - Expected: check_copy_budget("commit_scene", 0, [], 0).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts a zero-budget function that copies nothing")
step("Verify: accepts a zero-budget function that copies nothing")
expect(check_copy_budget("commit_scene", 0, [], 0).len()).to_equal(0)
```

</details>

#### does not check an unannotated function

- does not check an unannotated function
- Verify: does not check an unannotated function
   - Expected: v.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not check an unannotated function")
step("Verify: does not check an unannotated function")
# Opt-in, exactly like @noalloc. A 4KB copy in an unannotated
# function is not this pass's business.
val v = check_copy_budget("free_fn", COPY_BUDGET_UNSET, [copy("Style", 4096)], 0)
expect(v.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### @copy_budget — rejected

#### rejects a copy over budget

- rejects a copy over budget
- Verify: rejects a copy over budget
   - Expected: v.len() equals `1`
   - Expected: v[0].kind equals `EFFECT_COPY_OVER_BUDGET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a copy over budget")
step("Verify: rejects a copy over budget")
val v = check_copy_budget("blit_row", 8, [copy("Rect", 16)], 0)
expect(v.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(v[0].kind).to_equal(EFFECT_COPY_OVER_BUDGET)
```

</details>

#### rejects an implicit whole-struct copy under budget 0

- rejects an implicit whole-struct copy under budget 0
- Verify: rejects an implicit whole-struct copy under budget 0
   - Expected: v.len() equals `2`
   - Expected: v[0].kind equals `EFFECT_IMPLICIT_COPY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an implicit whole-struct copy under budget 0")
step("Verify: rejects an implicit whole-struct copy under budget 0")
# Two violations: the implicit copy on sight, and the budget breach.
val v = check_copy_budget("commit_scene", 0, [implicit_copy("Style", 1408)], 0)
expect(v.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(v[0].kind).to_equal(EFFECT_IMPLICIT_COPY)
assert_true(v[0].detail.contains("implicit whole-value copy"))
```

</details>

#### rejects a caller whose CALLEE blows the budget

- rejects a caller whose CALLEE blows the budget
- Verify: rejects a caller whose CALLEE blows the budget
   - Expected: v.len() equals `1`
   - Expected: v[0].kind equals `EFFECT_COPY_OVER_BUDGET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a caller whose CALLEE blows the budget")
step("Verify: rejects a caller whose CALLEE blows the budget")
# The body itself copies 8 bytes and would pass in isolation.
# This is the transitive check: without it, the example goes green.
val v = check_copy_budget("outer", 16, [copy("i64", 8)], 4096)
expect(v.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(v[0].kind).to_equal(EFFECT_COPY_OVER_BUDGET)
assert_true(v[0].detail.contains("4096 from callees"))
```

</details>

### transitive closure

#### charges a caller for its whole callee chain

- charges a caller for its whole callee chain
- Verify: charges a caller for its whole callee chain
   - Expected: t[0] equals `111`
   - Expected: t[1] equals `110`
   - Expected: t[2] equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("charges a caller for its whole callee chain")
step("Verify: charges a caller for its whole callee chain")
# top -> mid -> leaf, own cost 1 / 10 / 100.
val t = effect_copy_closure(["top", "mid", "leaf"], [1, 10, 100],
    [["mid"], ["leaf"], []])
expect(t[0]).to_equal(111)  # oracle: 111 — named expected value from the requirement
expect(t[1]).to_equal(110)  # oracle: 110 — named expected value from the requirement
expect(t[2]).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>

#### saturates a recursive cycle instead of diverging

- saturates a recursive cycle instead of diverging
- Verify: saturates a recursive cycle instead of diverging


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("saturates a recursive cycle instead of diverging")
step("Verify: saturates a recursive cycle instead of diverging")
# a -> b -> a. Fail-closed: saturation breaches every finite budget.
val t = effect_copy_closure(["a", "b"], [1, 1], [["b"], ["a"]])
assert_true(t[0] > 1000)
```

</details>

#### ignores calls to functions outside the unit

- ignores calls to functions outside the unit
- Verify: ignores calls to functions outside the unit
   - Expected: t[0] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ignores calls to functions outside the unit")
step("Verify: ignores calls to functions outside the unit")
val t = effect_copy_closure(["a"], [5], [["unknown_extern"]])
expect(t[0]).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

### @bounded_loop — accepted

<details>
<summary>Advanced: accepts a capacity-bounded loop</summary>

#### accepts a capacity-bounded loop

- accepts a capacity-bounded loop
- Verify: accepts a capacity-bounded loop
   - Expected: check_bounded_loops("raster", true, [loop_ok("for tile in tiles")]).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts a capacity-bounded loop")
step("Verify: accepts a capacity-bounded loop")
expect(check_bounded_loops("raster", true, [loop_ok("for tile in tiles")]).len()).to_equal(0)
```

</details>


</details>

#### does not check an unannotated function

- does not check an unannotated function
- Verify: does not check an unannotated function
   - Expected: check_bounded_loops("repl", false, [loop_unbounded("while true")]).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not check an unannotated function")
step("Verify: does not check an unannotated function")
expect(check_bounded_loops("repl", false, [loop_unbounded("while true")]).len()).to_equal(0)
```

</details>

### @bounded_loop — rejected

<details>
<summary>Advanced: rejects a loop with no provable bound</summary>

#### rejects a loop with no provable bound

- rejects a loop with no provable bound
- Verify: rejects a loop with no provable bound
   - Expected: v.len() equals `1`
   - Expected: v[0].kind equals `EFFECT_UNBOUNDED_LOOP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a loop with no provable bound")
step("Verify: rejects a loop with no provable bound")
val v = check_bounded_loops("raster", true, [loop_unbounded("while true")])
expect(v.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(v[0].kind).to_equal(EFFECT_UNBOUNDED_LOOP)
```

</details>


</details>

#### rejects unbounded container growth even when the trip count is bounded

- rejects unbounded container growth even when the trip count is bounded
- Verify: rejects unbounded container growth even when the trip count is bounded
   - Expected: v.len() equals `1`
   - Expected: v[0].kind equals `EFFECT_GROWTH_IN_LOOP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects unbounded container growth even when the trip count is bounded")
step("Verify: rejects unbounded container growth even when the trip count is bounded")
val v = check_bounded_loops("raster", true, [loop_growing("for i in 0..64")])
expect(v.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(v[0].kind).to_equal(EFFECT_GROWTH_IN_LOOP)
```

</details>

### manifest and diagnostics

#### treats an unknown function as unannotated

- treats an unknown function as unannotated
- Verify: treats an unknown function as unannotated


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats an unknown function as unannotated")
step("Verify: treats an unknown function as unannotated")
val m = EffectManifest.new()
expect_not(m.has_copy_budget("never_registered"))
```

</details>

#### reports a registered budget

- reports a registered budget
- Verify: reports a registered budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a registered budget")
step("Verify: reports a registered budget")
val m = EffectManifest.new()
m.register("commit", 0, true, 0)
assert_true(m.has_copy_budget("commit"))
```

</details>

#### formats a violation as an error[effect] diagnostic

- formats a violation as an error[effect] diagnostic
- Verify: formats a violation as an error[effect] diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats a violation as an error[effect] diagnostic")
step("Verify: formats a violation as an error[effect] diagnostic")
val v = check_copy_budget("blit_row", 8, [copy("Rect", 16)], 0)
assert_true(format_effect_violation(v[0]).starts_with("error[effect]"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-SEMANTICS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fbcf0b1341d9ac5df78a762b31337532572970cdb259414a0c635f346f69f13d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fbcf0b1341d9ac5df78a762b31337532572970cdb259414a0c635f346f69f13d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fbcf0b1341d9ac5df78a762b31337532572970cdb259414a0c635f346f69f13d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantics/effect_verifier_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/effect_verifier_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/effect_verifier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/effect_verifier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/effect_verifier_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/effect_verifier_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts copies that fit the budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/effect_verifier_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a zero-budget function that copies nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/effect_verifier_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not check an unannotated function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
