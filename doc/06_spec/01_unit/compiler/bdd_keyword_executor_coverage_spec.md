# Bdd Keyword Executor Coverage Specification

> Tests covering BDD keyword executor coverage (defect class: advertised != executed).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bdd Keyword Executor Coverage Specification

## Scenarios

### BDD keyword executor coverage (defect class: advertised != executed)

#### finds a non-empty advertised group-keyword list to check against

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds a non-empty advertised group-keyword list to check against
   - Expected: src.len() > 0 is true
   - Expected: names.len() > 0 is true
   - Expected: names contains `describe`
   - Expected: names contains `feature`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a non-empty advertised group-keyword list to check against")
val src = rt_file_read_text(ANALYZER_PATH) ?? ""
expect(src.len() > 0).to_equal(true)
val names = advertised_group_keywords(src)
# Vacuity guard: an empty list would make every assertion below trivially
# true, which is exactly how the original defect stayed invisible.
expect(names.len() > 0).to_equal(true)
expect(names.contains("describe")).to_equal(true)
expect(names.contains("feature")).to_equal(true)
```

</details>

#### wires every advertised group keyword into the interpreter lane

- wires every advertised group keyword into the interpreter lane
   - Expected: interp.len() > 0 is true
   - Expected: interp contains `"" + kw + ""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires every advertised group keyword into the interpreter lane")
val names = advertised_group_keywords(rt_file_read_text(ANALYZER_PATH) ?? "")
val interp = rt_file_read_text(INTERP_PATH) ?? ""
expect(interp.len() > 0).to_equal(true)
for kw in names:
    expect(interp.contains("\"" + kw + "\"")).to_equal(true)
```

</details>

#### wires every advertised group keyword into the HIR/JIT lowering lane

- wires every advertised group keyword into the HIR/JIT lowering lane
   - Expected: lower.len() > 0 is true
   - Expected: lower contains `"" + kw + ""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires every advertised group keyword into the HIR/JIT lowering lane")
val names = advertised_group_keywords(rt_file_read_text(ANALYZER_PATH) ?? "")
val lower = rt_file_read_text(LOWER_PATH) ?? ""
expect(lower.len() > 0).to_equal(true)
for kw in names:
    expect(lower.contains("\"" + kw + "\"")).to_equal(true)
```

</details>

#### registers every advertised group keyword as a Testing builtin

- registers every advertised group keyword as a Testing builtin
   - Expected: reg.len() > 0 is true
   - Expected: reg contains `self.register("" + kw + "", BuiltinCategory.Testing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers every advertised group keyword as a Testing builtin")
val names = advertised_group_keywords(rt_file_read_text(ANALYZER_PATH) ?? "")
val reg = rt_file_read_text(REGISTRY_PATH) ?? ""
expect(reg.len() > 0).to_equal(true)
for kw in names:
    expect(reg.contains("self.register(\"" + kw + "\", BuiltinCategory.Testing")).to_equal(true)
```

</details>

#### binds every advertised group keyword in the type checker environment

- binds every advertised group keyword in the type checker environment
   - Expected: checker.len() > 0 is true
   - Expected: checker contains `"" + kw + ""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds every advertised group keyword in the type checker environment")
val names = advertised_group_keywords(rt_file_read_text(ANALYZER_PATH) ?? "")
val checker = rt_file_read_text(CHECKER_PATH) ?? ""
expect(checker.len() > 0).to_equal(true)
for kw in names:
    expect(checker.contains("\"" + kw + "\"")).to_equal(true)
```

</details>

#### keeps the example-level keyword set identical across both executor lanes

- keeps the example-level keyword set identical across both executor lanes
   - Expected: interp contains `"" + kw + ""`
   - Expected: lower contains `"" + kw + ""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the example-level keyword set identical across both executor lanes")
# Same class, other half: `it`/`test`/`example`/`specify` are the
# example-level aliases. If one lane grows an alias the other lacks,
# a spec goes green in the interpreter and dies under JIT (or vice
# versa) -- silent, lane-dependent example loss.
val interp = rt_file_read_text(INTERP_PATH) ?? ""
val lower = rt_file_read_text(LOWER_PATH) ?? ""
for kw in ["it", "test", "example", "specify", "slow_it"]:
    expect(interp.contains("\"" + kw + "\"")).to_equal(true)
    expect(lower.contains("\"" + kw + "\"")).to_equal(true)
```

</details>

#### documents limited_it as a KNOWN, deliberate lane asymmetry

- documents limited_it as a KNOWN, deliberate lane asymmetry
   - Expected: interp contains `"limited_it"`
   - Expected: lower does not contain `"limited_it"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents limited_it as a KNOWN, deliberate lane asymmetry")
# `limited_it` is intentionally interpreter-only: it carries a
# `resource_limits` named argument and the HIR/JIT lane has no runtime
# hook to enforce it, so wiring it up there would silently drop the
# limits (a fail-open) rather than fix anything. This example pins the
# asymmetry as DELIBERATE so it cannot be mistaken for the bug above,
# and turns RED if someone wires it up without a limits hook.
val interp = rt_file_read_text(INTERP_PATH) ?? ""
val lower = rt_file_read_text(LOWER_PATH) ?? ""
expect(interp.contains("\"limited_it\"")).to_equal(true)
expect(lower.contains("\"limited_it\"")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bdd_keyword_executor_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BDD keyword executor coverage (defect class: advertised != executed).
- BDD keyword executor coverage (defect class: advertised != executed)

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

- Canonical SPipe generation for source `d832353dd46dc2efb32b841064b78b92d8153aebd9648bbc28526bd95460a9a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d832353dd46dc2efb32b841064b78b92d8153aebd9648bbc28526bd95460a9a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d832353dd46dc2efb32b841064b78b92d8153aebd9648bbc28526bd95460a9a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bdd_keyword_executor_coverage_spec.spl
mirror: doc/06_spec/01_unit/compiler/bdd_keyword_executor_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bdd_keyword_executor_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bdd_keyword_executor_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bdd_keyword_executor_coverage_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a non-empty advertised group-keyword list to check against' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_keyword_executor_coverage_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wires every advertised group keyword into the interpreter lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_keyword_executor_coverage_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wires every advertised group keyword into the HIR/JIT lowering lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
