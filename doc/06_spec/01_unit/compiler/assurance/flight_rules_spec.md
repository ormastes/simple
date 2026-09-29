# flight_rules_spec

> Purpose: Prove that FlightRuleV1 registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# flight_rules_spec

Purpose: Prove that FlightRuleV1 registry.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/flight_rules_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that FlightRuleV1 registry.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### FlightRuleV1 registry

### identity

#### is non-empty and covers every category

- is non-empty and covers every category
- Verify: is non-empty and covers every category
   - Expected: flight_rules().len() > 0 is true
   - Expected: flight_rules_in_category(RuleCategory.ControlFlow).len() > 0 is true
   - Expected: flight_rules_in_category(RuleCategory.Memory).len() > 0 is true
   - Expected: flight_rules_in_category(RuleCategory.Data).len() > 0 is true
   - Expected: flight_rules_in_category(RuleCategory.Abstraction).len() > 0 is true
   - Expected: flight_rules_in_category(RuleCategory.MatchCoverage).len() > 0 is true
   - Expected: flight_rules_in_category(RuleCategory.Implementation).len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is non-empty and covers every category")
step("Verify: is non-empty and covers every category")
# @req: REQ-COMP-FLIGHTRULEV1-REGISTRY-001
expect(flight_rules().len() > 0).to_equal(true)
expect(flight_rules_in_category(RuleCategory.ControlFlow).len() > 0).to_equal(true)
expect(flight_rules_in_category(RuleCategory.Memory).len() > 0).to_equal(true)
expect(flight_rules_in_category(RuleCategory.Data).len() > 0).to_equal(true)
expect(flight_rules_in_category(RuleCategory.Abstraction).len() > 0).to_equal(true)
expect(flight_rules_in_category(RuleCategory.MatchCoverage).len() > 0).to_equal(true)
expect(flight_rules_in_category(RuleCategory.Implementation).len() > 0).to_equal(true)
```

</details>

#### gives every rule an FLT- prefixed id

- gives every rule an FLT- prefixed id
- Verify: gives every rule an FLT- prefixed id
   - Expected: bad equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives every rule an FLT- prefixed id")
step("Verify: gives every rule an FLT- prefixed id")
val rules = flight_rules()
var bad = 0
var i = 0
while i < rules.len():
    if not rules[i].id.starts_with("FLT-"):
        bad = bad + 1
    i = i + 1
expect(bad).to_equal(0)
```

</details>

#### has unique rule ids

- has unique rule ids
- Verify: has unique rule ids
   - Expected: dups equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has unique rule ids")
step("Verify: has unique rule ids")
val rules = flight_rules()
var dups = 0
var i = 0
while i < rules.len():
    var j = i + 1
    while j < rules.len():
        if rules[i].id == rules[j].id:
            dups = dups + 1
        j = j + 1
    i = i + 1
expect(dups).to_equal(0)
```

</details>

#### has unique diagnostic codes, ignoring the '-' placeholder

- has unique diagnostic codes, ignoring the '-' placeholder
- Verify: has unique diagnostic codes, ignoring the '-' placeholder
   - Expected: dups equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has unique diagnostic codes, ignoring the '-' placeholder")
step("Verify: has unique diagnostic codes, ignoring the '-' placeholder")
val rules = flight_rules()
var dups = 0
var i = 0
while i < rules.len():
    var j = i + 1
    while j < rules.len():
        if rules[i].diagnostic != "-" and rules[i].diagnostic == rules[j].diagnostic:
            dups = dups + 1
        j = j + 1
    i = i + 1
expect(dups).to_equal(0)
```

</details>

#### finds a rule by id and returns nil for an unknown id

- finds a rule by id and returns nil for an unknown id
- Verify: finds a rule by id and returns nil for an unknown id
   - Expected: hit_known is true
   - Expected: found.title.starts_with("No goto") is true
   - Expected: hit_unknown is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds a rule by id and returns nil for an unknown id")
step("Verify: finds a rule by id and returns nil for an unknown id")
# `.?` in CONDITION position is the specified presence test. Two
# weaker forms were tried first and both give a WRONG answer here:
#   * `expect(opt.?).to_equal(false)` — `.?` in VALUE position is
#     specified to return `T?`, so an absent optional yields nil,
#     not false.
#   * `if opt:` (bare optional as a condition) takes the PRESENT
#     branch for an absent optional, because RT_NIL is sentinel 3
#     and therefore truthy. Open defect:
#     doc/08_tracking/bug/bare_optional_in_condition_position_wrong_branch_2026-08-01.md
var hit_known = false
if find_flight_rule("FLT-CF-001").?:
    hit_known = true
expect(hit_known).to_equal(true)
val found = find_flight_rule("FLT-CF-001")
if found:
    expect(found.title.starts_with("No goto")).to_equal(true)
var hit_unknown = false
if find_flight_rule("FLT-NOPE-999").?:
    hit_unknown = true
expect(hit_unknown).to_equal(false)
```

</details>

### field completeness

#### leaves no field of any rule empty

- leaves no field of any rule empty
- Verify: leaves no field of any rule empty
   - Expected: bad equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves no field of any rule empty")
step("Verify: leaves no field of any rule empty")
val rules = flight_rules()
var bad = 0
var i = 0
while i < rules.len():
    val r = rules[i]
    if r.title.len() == 0:
        bad = bad + 1
    if r.sources.len() == 0:
        bad = bad + 1
    if r.analyzer.len() == 0:
        bad = bad + 1
    if r.diagnostic.len() == 0:
        bad = bad + 1
    if r.fix.len() == 0:
        bad = bad + 1
    i = i + 1
expect(bad).to_equal(0)
```

</details>

#### gives every non-intrinsic rule a real diagnostic code

- gives every non-intrinsic rule a real diagnostic code
- Verify: gives every non-intrinsic rule a real diagnostic code
   - Expected: bad equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives every non-intrinsic rule a real diagnostic code")
step("Verify: gives every non-intrinsic rule a real diagnostic code")
val rules = flight_rules()
var bad = 0
var i = 0
while i < rules.len():
    val r = rules[i]
    val is_intrinsic = r.critical_level.name() == "intrinsic"
    if not is_intrinsic and r.diagnostic == "-":
        bad = bad + 1
    i = i + 1
expect(bad).to_equal(0)
```

</details>

### grade ladder

#### is monotone: a higher grade never relaxes a rule

- is monotone: a higher grade never relaxes a rule
- Verify: is monotone: a higher grade never relaxes a rule
   - Expected: violations equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is monotone: a higher grade never relaxes a rule")
step("Verify: is monotone: a higher grade never relaxes a rule")
val rules = flight_rules()
var violations = 0
var i = 0
while i < rules.len():
    val r = rules[i]
    if r.aero_a_level.rank() < r.critical_level.rank():
        violations = violations + 1
    if r.space_a_level.rank() < r.aero_a_level.rank():
        violations = violations + 1
    i = i + 1
expect(violations).to_equal(0)
```

</details>

### analyzer honesty

#### separates intrinsic rules from unfilled enforcement gaps

- separates intrinsic rules from unfilled enforcement gaps
- Verify: separates intrinsic rules from unfilled enforcement gaps
   - Expected: cf1.analyzer equals `none`
   - Expected: cf1.is_enforcement_gap() is false
   - Expected: cf3.analyzer equals `none`
   - Expected: cf3.is_enforcement_gap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("separates intrinsic rules from unfilled enforcement gaps")
step("Verify: separates intrinsic rules from unfilled enforcement gaps")
# FLT-CF-001 has no analyzer because the grammar has no goto.
# FLT-CF-003 has no analyzer because nobody wrote one.
val cf1 = find_flight_rule("FLT-CF-001")
val cf3 = find_flight_rule("FLT-CF-003")
if cf1:
    expect(cf1.analyzer).to_equal("none")
    expect(cf1.is_enforcement_gap()).to_equal(false)
if cf3:
    expect(cf3.analyzer).to_equal("none")
    expect(cf3.is_enforcement_gap()).to_equal(true)
```

</details>

#### names the twin that actually fires, not the dead semantic checker

- names the twin that actually fires, not the dead semantic checker
- Verify: names the twin that actually fires, not the dead semantic checker
   - Expected: imp1.analyzer.starts_with("lint.text.") is true
   - Expected: imp1.is_enforcement_gap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the twin that actually fires, not the dead semantic checker")
step("Verify: names the twin that actually fires, not the dead semantic checker")
# Plan premises 12b/13: the LIVE emitters are the text
# reimplementations in 90.tools/lint, not 35.semantics/lint.
val imp1 = find_flight_rule("FLT-IMP-001")
if imp1:
    expect(imp1.analyzer.starts_with("lint.text.")).to_equal(true)
    expect(imp1.is_enforcement_gap()).to_equal(false)
```

</details>

#### reports enforcement gaps as a strict subset of the registry

- reports enforcement gaps as a strict subset of the registry
- Verify: reports enforcement gaps as a strict subset of the registry
   - Expected: gaps.len() > 0 is true
   - Expected: gaps.len() < flight_rules().len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports enforcement gaps as a strict subset of the registry")
step("Verify: reports enforcement gaps as a strict subset of the registry")
val gaps = flight_rule_enforcement_gaps()
expect(gaps.len() > 0).to_equal(true)
expect(gaps.len() < flight_rules().len()).to_equal(true)
```

</details>

### rule-set hash

#### is deterministic across calls

- is deterministic across calls
- Verify: is deterministic across calls
   - Expected: flight_rules_hash() equals `flight_rules_hash()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is deterministic across calls")
step("Verify: is deterministic across calls")
expect(flight_rules_hash()).to_equal(flight_rules_hash())
```

</details>

#### is sensitive to the registry text

- is sensitive to the registry text
- Verify: is sensitive to the registry text
   - Expected: base == perturbed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is sensitive to the registry text")
step("Verify: is sensitive to the registry text")
val base = assurance_text_hash(flight_rules_canonical_text())
val perturbed = assurance_text_hash(flight_rules_canonical_text() + "x")
expect(base == perturbed).to_equal(false)
```

</details>

#### distinguishes inputs that differ only by field order

- distinguishes inputs that differ only by field order
- Verify: distinguishes inputs that differ only by field order
   - Expected: assurance_text_hash("a|b") == assurance_text_hash("b|a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("distinguishes inputs that differ only by field order")
step("Verify: distinguishes inputs that differ only by field order")
expect(assurance_text_hash("a|b") == assurance_text_hash("b|a")).to_equal(false)
```

</details>

### flight-rule docgen

#### emits one crosswalk row per rule

- emits one crosswalk row per rule
- Verify: emits one crosswalk row per rule
   - Expected: count_lines_starting_with(doc, "| `FLT-") equals `flight_rules().len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits one crosswalk row per rule")
step("Verify: emits one crosswalk row per rule")
val doc = render_standards_crosswalk()
expect(count_lines_starting_with(doc, "| `FLT-")).to_equal(flight_rules().len())
```

</details>

#### emits one severity row per rule

- emits one severity row per rule
- Verify: emits one severity row per rule
   - Expected: count_lines_starting_with(doc, "| `FLT-") equals `flight_rules().len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits one severity row per rule")
step("Verify: emits one severity row per rule")
val doc = render_severity_table()
expect(count_lines_starting_with(doc, "| `FLT-")).to_equal(flight_rules().len())
```

</details>

#### carries the unverified-citation marker in the crosswalk

- carries the unverified-citation marker in the crosswalk
- Verify: carries the unverified-citation marker in the crosswalk
   - Expected: doc contains `source_verification_note()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries the unverified-citation marker in the crosswalk")
step("Verify: carries the unverified-citation marker in the crosswalk")
val doc = render_standards_crosswalk()
expect(doc.contains(source_verification_note())).to_equal(true)
```

</details>

#### stamps both tables with the rule-set hash

- stamps both tables with the rule-set hash
- Verify: stamps both tables with the rule-set hash
   - Expected: render_standards_crosswalk() contains `flight_rules_hash()`
   - Expected: render_severity_table() contains `flight_rules_hash()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stamps both tables with the rule-set hash")
step("Verify: stamps both tables with the rule-set hash")
expect(render_standards_crosswalk().contains(flight_rules_hash())).to_equal(true)
expect(render_severity_table().contains(flight_rules_hash())).to_equal(true)
```

</details>

#### renders a specific rule row with its generated severity ladder

- renders a specific rule row with its generated severity ladder
- Verify: renders a specific rule row with its generated severity ladder
   - Expected: doc contains `| `FLT-MEM-001` | shall | shall | shall |`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders a specific rule row with its generated severity ladder")
step("Verify: renders a specific rule row with its generated severity ladder")
val doc = render_severity_table()
expect(doc.contains("| `FLT-MEM-001` | shall | shall | shall |")).to_equal(true)
```

</details>

#### counts wired, intrinsic and gap rules separately

- counts wired, intrinsic and gap rules separately
- Verify: counts wired, intrinsic and gap rules separately
   - Expected: doc contains `32 total`
   - Expected: doc contains `2 with a live analyzer`
   - Expected: doc contains `2 intrinsic (no analyzer needed)`
   - Expected: doc contains `28 unfilled gaps`
   - Expected: flight_rule_enforcement_gaps().len() equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts wired, intrinsic and gap rules separately")
step("Verify: counts wired, intrinsic and gap rules separately")
# The three-way split is what WP-2's census keys off. Row-count alone
# would still pass if `wired` and `intrinsic` were swapped, so the
# counters are asserted directly. Hardcoded on purpose: the registry is
# frozen, and adding a rule SHOULD break this and force a conscious
# update to the crosswalk.
val doc = render_enforcement_gap_report()
expect(doc.contains("32 total")).to_equal(true)
expect(doc.contains("2 with a live analyzer")).to_equal(true)
expect(doc.contains("2 intrinsic (no analyzer needed)")).to_equal(true)
expect(doc.contains("28 unfilled gaps")).to_equal(true)
expect(flight_rule_enforcement_gaps().len()).to_equal(28)
```

</details>

#### lists exactly the enforcement gaps in the gap report

- lists exactly the enforcement gaps in the gap report
- Verify: lists exactly the enforcement gaps in the gap report
   - Expected: count_lines_starting_with(doc, "| `FLT-") equals `flight_rule_enforcement_gaps().len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lists exactly the enforcement gaps in the gap report")
step("Verify: lists exactly the enforcement gaps in the gap report")
val doc = render_enforcement_gap_report()
expect(count_lines_starting_with(doc, "| `FLT-")).to_equal(flight_rule_enforcement_gaps().len())
```

</details>

### flight-rule enum round-trips

#### round-trips every RuleCategory through name/from_name

- round-trips every RuleCategory through name/from_name
- Verify: round-trips every RuleCategory through name/from_name
   - Expected: RuleCategory.from_name(RuleCategory.ControlFlow.name()).name() equals `control_flow`
   - Expected: RuleCategory.from_name(RuleCategory.Memory.name()).name() equals `memory`
   - Expected: RuleCategory.from_name(RuleCategory.Data.name()).name() equals `data`
   - Expected: RuleCategory.from_name(RuleCategory.Abstraction.name()).name() equals `abstraction`
   - Expected: RuleCategory.from_name(RuleCategory.MatchCoverage.name()).name() equals `match_coverage`
   - Expected: RuleCategory.from_name(RuleCategory.Implementation.name()).name() equals `implementation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips every RuleCategory through name/from_name")
step("Verify: round-trips every RuleCategory through name/from_name")
expect(RuleCategory.from_name(RuleCategory.ControlFlow.name()).name()).to_equal("control_flow")
expect(RuleCategory.from_name(RuleCategory.Memory.name()).name()).to_equal("memory")
expect(RuleCategory.from_name(RuleCategory.Data.name()).name()).to_equal("data")
expect(RuleCategory.from_name(RuleCategory.Abstraction.name()).name()).to_equal("abstraction")
expect(RuleCategory.from_name(RuleCategory.MatchCoverage.name()).name()).to_equal("match_coverage")
expect(RuleCategory.from_name(RuleCategory.Implementation.name()).name()).to_equal("implementation")
```

</details>

#### round-trips every EnforcementPhase

- round-trips every EnforcementPhase
- Verify: round-trips every EnforcementPhase
   - Expected: EnforcementPhase.from_name("compile").name() equals `compile`
   - Expected: EnforcementPhase.from_name("integration").name() equals `integration`
   - Expected: EnforcementPhase.from_name("release").name() equals `release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips every EnforcementPhase")
step("Verify: round-trips every EnforcementPhase")
expect(EnforcementPhase.from_name("compile").name()).to_equal("compile")
expect(EnforcementPhase.from_name("integration").name()).to_equal("integration")
expect(EnforcementPhase.from_name("release").name()).to_equal("release")
```

</details>

#### round-trips every RuleLevel

- round-trips every RuleLevel
- Verify: round-trips every RuleLevel
   - Expected: RuleLevel.from_name("intrinsic").name() equals `intrinsic`
   - Expected: RuleLevel.from_name("shall").name() equals `shall`
   - Expected: RuleLevel.from_name("will").name() equals `will`
   - Expected: RuleLevel.from_name("should").name() equals `should`
   - Expected: RuleLevel.from_name("evidence").name() equals `evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips every RuleLevel")
step("Verify: round-trips every RuleLevel")
expect(RuleLevel.from_name("intrinsic").name()).to_equal("intrinsic")
expect(RuleLevel.from_name("shall").name()).to_equal("shall")
expect(RuleLevel.from_name("will").name()).to_equal("will")
expect(RuleLevel.from_name("should").name()).to_equal("should")
expect(RuleLevel.from_name("evidence").name()).to_equal("evidence")
```

</details>

#### ranks intrinsic above shall above will above should

- ranks intrinsic above shall above will above should
- Verify: ranks intrinsic above shall above will above should
   - Expected: RuleLevel.Intrinsic.rank() > RuleLevel.Shall.rank() is true
   - Expected: RuleLevel.Shall.rank() > RuleLevel.Will.rank() is true
   - Expected: RuleLevel.Will.rank() > RuleLevel.Should.rank() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ranks intrinsic above shall above will above should")
step("Verify: ranks intrinsic above shall above will above should")
expect(RuleLevel.Intrinsic.rank() > RuleLevel.Shall.rank()).to_equal(true)
expect(RuleLevel.Shall.rank() > RuleLevel.Will.rank()).to_equal(true)
expect(RuleLevel.Will.rank() > RuleLevel.Should.rank()).to_equal(true)
```

</details>

#### round-trips every DeviationPolicy

- round-trips every DeviationPolicy
- Verify: round-trips every DeviationPolicy
   - Expected: DeviationPolicy.from_name("prohibited").name() equals `prohibited`
   - Expected: DeviationPolicy.from_name("reviewed_waiver").name() equals `reviewed_waiver`
   - Expected: DeviationPolicy.from_name("project_approval").name() equals `project_approval`
   - Expected: DeviationPolicy.from_name("not_applicable").name() equals `not_applicable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips every DeviationPolicy")
step("Verify: round-trips every DeviationPolicy")
expect(DeviationPolicy.from_name("prohibited").name()).to_equal("prohibited")
expect(DeviationPolicy.from_name("reviewed_waiver").name()).to_equal("reviewed_waiver")
expect(DeviationPolicy.from_name("project_approval").name()).to_equal("project_approval")
expect(DeviationPolicy.from_name("not_applicable").name()).to_equal("not_applicable")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-FLIGHTRULEV1-REGISTRY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8eea00c60b9a73fe2fb3753c32c9da22e0fa0768f3cd78d463d941839624e69e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8eea00c60b9a73fe2fb3753c32c9da22e0fa0768f3cd78d463d941839624e69e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8eea00c60b9a73fe2fb3753c32c9da22e0fa0768f3cd78d463d941839624e69e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/assurance/flight_rules_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/flight_rules_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/flight_rules_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/flight_rules_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/flight_rules_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/assurance/flight_rules_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is non-empty and covers every category' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/flight_rules_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives every rule an FLT- prefixed id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/flight_rules_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has unique rule ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
