# aop_weaving_config_spec

> Purpose: Prove that AOP Weaving Config.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# aop_weaving_config_spec

Purpose: Prove that AOP Weaving Config.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/aop_weaving_config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AOP Weaving Config.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### AOP Weaving Config

### WeavingConfig.disabled

#### creates disabled config with no rules

- creates disabled config with no rules
- Verify: creates disabled config with no rules
   - Expected: config.enabled is false
   - Expected: weavingconfig_all_rules(config).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates disabled config with no rules")
step("Verify: creates disabled config with no rules")
# @req: REQ-COMPILER-FRONTEND-001
val config = WeavingConfig.disabled()
expect(config.enabled).to_equal(false)
expect(weavingconfig_all_rules(config).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### WeavingConfig.from_rules

#### creates enabled config when rules present

- creates enabled config when rules present
- Verify: creates enabled config when rules present
   - Expected: config.enabled is true
   - Expected: config.before_advices.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates enabled config when rules present")
step("Verify: creates enabled config when rules present")
val rules = [
    WeavingRule(predicate_text: "*", advice_function: "log_fn", form: AdviceForm.Before, priority: 10)
]
val config = WeavingConfig.from_rules(rules)
expect(config.enabled).to_equal(true)
expect(config.before_advices.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### creates disabled config with empty rules

- creates disabled config with empty rules
- Verify: creates disabled config with empty rules
   - Expected: config.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates disabled config with empty rules")
step("Verify: creates disabled config with empty rules")
val config = WeavingConfig.from_rules([])
expect(config.enabled).to_equal(false)
```

</details>

#### categorizes rules by advice form

- categorizes rules by advice form
- Verify: categorizes rules by advice form
   - Expected: config.before_advices.len() equals `1`
   - Expected: config.after_success_advices.len() equals `1`
   - Expected: config.after_error_advices.len() equals `1`
   - Expected: config.around_advices.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("categorizes rules by advice form")
step("Verify: categorizes rules by advice form")
val rules = [
    WeavingRule(predicate_text: "*", advice_function: "before_fn", form: AdviceForm.Before, priority: 10),
    WeavingRule(predicate_text: "*", advice_function: "after_fn", form: AdviceForm.AfterSuccess, priority: 10),
    WeavingRule(predicate_text: "*", advice_function: "error_fn", form: AdviceForm.AfterError, priority: 10),
    WeavingRule(predicate_text: "*", advice_function: "around_fn", form: AdviceForm.Around, priority: 10)
]
val config = WeavingConfig.from_rules(rules)
expect(config.before_advices.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(config.after_success_advices.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(config.after_error_advices.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(config.around_advices.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### matches_predicate

#### matches wildcard predicate

- matches wildcard predicate
- Verify: matches wildcard predicate
   - Expected: matches_predicate("*", ctx) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches wildcard predicate")
step("Verify: matches wildcard predicate")
val ctx = JoinPointContext(function_name: "foo", module_path: "mod", signature: "", attributes: [], effects: [])
expect(matches_predicate("*", ctx)).to_equal(true)
```

</details>

#### matches exact function name

- matches exact function name
- Verify: matches exact function name
   - Expected: matches_predicate("my_func", ctx) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches exact function name")
step("Verify: matches exact function name")
val ctx = JoinPointContext(function_name: "my_func", module_path: "mod", signature: "", attributes: [], effects: [])
expect(matches_predicate("my_func", ctx)).to_equal(true)
```

</details>

#### rejects non-matching function name

- rejects non-matching function name
- Verify: rejects non-matching function name
   - Expected: matches_predicate("my_func", ctx) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects non-matching function name")
step("Verify: rejects non-matching function name")
val ctx = JoinPointContext(function_name: "other", module_path: "mod", signature: "", attributes: [], effects: [])
expect(matches_predicate("my_func", ctx)).to_equal(false)
```

</details>

#### matches attribute predicate

- matches attribute predicate
- Verify: matches attribute predicate
   - Expected: matches_predicate("@logged", ctx) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches attribute predicate")
step("Verify: matches attribute predicate")
val ctx = JoinPointContext(function_name: "foo", module_path: "mod", signature: "", attributes: ["logged"], effects: [])
expect(matches_predicate("@logged", ctx)).to_equal(true)
```

</details>

#### matches module predicate

- matches module predicate
- Verify: matches module predicate
   - Expected: matches_predicate("module:services.*", ctx) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches module predicate")
step("Verify: matches module predicate")
val ctx = JoinPointContext(function_name: "foo", module_path: "services.auth", signature: "", attributes: [], effects: [])
expect(matches_predicate("module:services.*", ctx)).to_equal(true)
```

</details>

### predicate_specificity

#### assigns wildcard lowest specificity

- assigns wildcard lowest specificity
- Verify: assigns wildcard lowest specificity
   - Expected: predicate_specificity("*") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns wildcard lowest specificity")
step("Verify: assigns wildcard lowest specificity")
expect(predicate_specificity("*")).to_equal(0)
```

</details>

#### assigns glob pattern specificity 1

- assigns glob pattern specificity 1
- Verify: assigns glob pattern specificity 1
   - Expected: predicate_specificity("foo*") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns glob pattern specificity 1")
step("Verify: assigns glob pattern specificity 1")
expect(predicate_specificity("foo*")).to_equal(1)
```

</details>

#### assigns attribute specificity 2

- assigns attribute specificity 2
- Verify: assigns attribute specificity 2
   - Expected: predicate_specificity("@logged") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns attribute specificity 2")
step("Verify: assigns attribute specificity 2")
expect(predicate_specificity("@logged")).to_equal(2)
```

</details>

#### assigns module specificity 3

- assigns module specificity 3
- Verify: assigns module specificity 3
   - Expected: predicate_specificity("module:services") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns module specificity 3")
step("Verify: assigns module specificity 3")
expect(predicate_specificity("module:services")).to_equal(3)
```

</details>

#### assigns exact name highest specificity

- assigns exact name highest specificity
- Verify: assigns exact name highest specificity
   - Expected: predicate_specificity("my_exact_func") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns exact name highest specificity")
step("Verify: assigns exact name highest specificity")
expect(predicate_specificity("my_exact_func")).to_equal(4)
```

</details>

### weave_function

#### returns empty result for disabled config

- returns empty result for disabled config
- Verify: returns empty result for disabled config
   - Expected: result.advices_inserted equals `0`
   - Expected: result.join_points_woven equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty result for disabled config")
step("Verify: returns empty result for disabled config")
val config = WeavingConfig.disabled()
val blocks: [MirBlockInfo] = []
val result = weave_function(config, "test_fn", "mod", [], [], blocks)
expect(result.advices_inserted).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.join_points_woven).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns empty result for function with no matching advice

- returns empty result for function with no matching advice
- Verify: returns empty result for function with no matching advice
   - Expected: result.advices_inserted equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty result for function with no matching advice")
step("Verify: returns empty result for function with no matching advice")
val rules = [
    WeavingRule(predicate_text: "specific_fn", advice_function: "log_fn", form: AdviceForm.Before, priority: 10)
]
val config = WeavingConfig.from_rules(rules)
val blocks = [MirBlockInfo(id: 0, instruction_kinds: [InstructionInfo(index: 0, kind_tag: "call")])]
val result = weave_function(config, "other_fn", "mod", [], [], blocks)
expect(result.advices_inserted).to_equal(0)  # oracle: 0 — named expected value from the requirement
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
- `REQ-COMPILER-FRONTEND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d954d5c398f319047e01caee48ba5d9a16ede04c9baf7f3bbe122ada2dea2ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d954d5c398f319047e01caee48ba5d9a16ede04c9baf7f3bbe122ada2dea2ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d954d5c398f319047e01caee48ba5d9a16ede04c9baf7f3bbe122ada2dea2ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/aop_weaving_config_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/aop_weaving_config_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/aop_weaving_config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/aop_weaving_config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/aop_weaving_config_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/aop_weaving_config_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates disabled config with no rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/aop_weaving_config_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates enabled config when rules present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/aop_weaving_config_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates disabled config with empty rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
