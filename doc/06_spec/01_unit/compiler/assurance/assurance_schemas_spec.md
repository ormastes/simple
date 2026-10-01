# Assurance Schemas Specification

> Tests covering ResolvedAssurancePolicyV1, strictness parsing, grade and convention, policy_hash, strictness comparison, ResolvedAssurancePolicyV2, CriticalSymbolSummaryV1, AssuranceStampV1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assurance Schemas Specification

## Scenarios

### ResolvedAssurancePolicyV1

### strictness parsing

#### accepts the canonical ladder names

- accepts the canonical ladder names
   - Expected: AssuranceStrictness.from_name("moderate").name() equals `moderate`
   - Expected: AssuranceStrictness.from_name("strict").name() equals `strict`
   - Expected: AssuranceStrictness.from_name("robust").name() equals `robust`
   - Expected: AssuranceStrictness.from_name("critical").name() equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts the canonical ladder names")
expect(AssuranceStrictness.from_name("moderate").name()).to_equal("moderate")
expect(AssuranceStrictness.from_name("strict").name()).to_equal("strict")
expect(AssuranceStrictness.from_name("robust").name()).to_equal("robust")
expect(AssuranceStrictness.from_name("critical").name()).to_equal("critical")
```

</details>

#### maps the frozen deprecated aliases onto canonical names

- maps the frozen deprecated aliases onto canonical names
   - Expected: AssuranceStrictness.from_name("mission-critical").name() equals `critical`
   - Expected: AssuranceStrictness.from_name("mission_critical").name() equals `critical`
   - Expected: AssuranceStrictness.from_name("reliable").name() equals `robust`
   - Expected: AssuranceStrictness.from_name("lib").name() equals `strict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps the frozen deprecated aliases onto canonical names")
expect(AssuranceStrictness.from_name("mission-critical").name()).to_equal("critical")
expect(AssuranceStrictness.from_name("mission_critical").name()).to_equal("critical")
expect(AssuranceStrictness.from_name("reliable").name()).to_equal("robust")
expect(AssuranceStrictness.from_name("lib").name()).to_equal("strict")
```

</details>

#### fails soft to moderate on an unknown or empty name

- fails soft to moderate on an unknown or empty name
   - Expected: AssuranceStrictness.from_name("").name() equals `moderate`
   - Expected: AssuranceStrictness.from_name("banana").name() equals `moderate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails soft to moderate on an unknown or empty name")
expect(AssuranceStrictness.from_name("").name()).to_equal("moderate")
expect(AssuranceStrictness.from_name("banana").name()).to_equal("moderate")
```

</details>

#### orders the ladder

- orders the ladder
   - Expected: AssuranceStrictness.Critical.at_least(AssuranceStrictness.Robust) is true
   - Expected: AssuranceStrictness.Robust.at_least(AssuranceStrictness.Critical) is false
   - Expected: AssuranceStrictness.Moderate.at_least(AssuranceStrictness.Moderate) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders the ladder")
expect(AssuranceStrictness.Critical.at_least(AssuranceStrictness.Robust)).to_equal(true)
expect(AssuranceStrictness.Robust.at_least(AssuranceStrictness.Critical)).to_equal(false)
expect(AssuranceStrictness.Moderate.at_least(AssuranceStrictness.Moderate)).to_equal(true)
```

</details>

### grade and convention

#### round-trips grades with both spellings

- round-trips grades with both spellings
   - Expected: AssuranceGrade.from_name("aero-a").name() equals `aero-a`
   - Expected: AssuranceGrade.from_name("aero_a").name() equals `aero-a`
   - Expected: AssuranceGrade.from_name("space-a").name() equals `space-a`
   - Expected: AssuranceGrade.from_name("nope").name() equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips grades with both spellings")
expect(AssuranceGrade.from_name("aero-a").name()).to_equal("aero-a")
expect(AssuranceGrade.from_name("aero_a").name()).to_equal("aero-a")
expect(AssuranceGrade.from_name("space-a").name()).to_equal("space-a")
expect(AssuranceGrade.from_name("nope").name()).to_equal("none")
```

</details>

#### round-trips conventions

- round-trips conventions
   - Expected: AssuranceConvention.from_name("flight-core-v1").name() equals `flight-core-v1`
   - Expected: AssuranceConvention.from_name("flight_core_v1").name() equals `flight-core-v1`
   - Expected: AssuranceConvention.from_name("").name() equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips conventions")
expect(AssuranceConvention.from_name("flight-core-v1").name()).to_equal("flight-core-v1")
expect(AssuranceConvention.from_name("flight_core_v1").name()).to_equal("flight-core-v1")
expect(AssuranceConvention.from_name("").name()).to_equal("none")
```

</details>

#### reports whether the FLT- registry is in force

- reports whether the FLT- registry is in force
   - Expected: flight_policy().flight_rules_active() is true
   - Expected: ResolvedAssurancePolicyV1.default().flight_rules_active() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports whether the FLT- registry is in force")
expect(flight_policy().flight_rules_active()).to_equal(true)
expect(ResolvedAssurancePolicyV1.default().flight_rules_active()).to_equal(false)
```

</details>

### policy_hash

#### is deterministic for two independently built identical policies

- is deterministic for two independently built identical policies
   - Expected: flight_policy().policy_hash() equals `flight_policy().policy_hash()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is deterministic for two independently built identical policies")
expect(flight_policy().policy_hash()).to_equal(flight_policy().policy_hash())
```

</details>

#### changes when strictness changes

- changes when strictness changes
   - Expected: p.policy_hash() == flight_policy().policy_hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes when strictness changes")
var p = flight_policy()
p.strictness = AssuranceStrictness.Robust
expect(p.policy_hash() == flight_policy().policy_hash()).to_equal(false)
```

</details>

#### changes when runtime_family changes

- changes when runtime_family changes
   - Expected: p.policy_hash() == flight_policy().policy_hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes when runtime_family changes")
var p = flight_policy()
p.runtime_family = "nogc_async_mut"
expect(p.policy_hash() == flight_policy().policy_hash()).to_equal(false)
```

</details>

#### changes when assurance_grade changes

- changes when assurance_grade changes
   - Expected: p.policy_hash() == flight_policy().policy_hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes when assurance_grade changes")
var p = flight_policy()
p.assurance_grade = AssuranceGrade.SpaceA
expect(p.policy_hash() == flight_policy().policy_hash()).to_equal(false)
```

</details>

#### changes when convention changes

- changes when convention changes
   - Expected: p.policy_hash() == flight_policy().policy_hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes when convention changes")
var p = flight_policy()
p.convention = AssuranceConvention.NoConvention
expect(p.policy_hash() == flight_policy().policy_hash()).to_equal(false)
```

</details>

#### carries the APOLV1 tag so a schema break is visible

- carries the APOLV1 tag so a schema break is visible
   - Expected: flight_policy().policy_hash().starts_with("APOLV1-") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries the APOLV1 tag so a schema break is visible")
expect(flight_policy().policy_hash().starts_with("APOLV1-")).to_equal(true)
```

</details>

### strictness comparison

#### never lets a weaker policy claim to dominate a stronger one

- never lets a weaker policy claim to dominate a stronger one
   - Expected: strong.is_at_least_as_strict_as(weak) is true
   - Expected: weak.is_at_least_as_strict_as(strong) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never lets a weaker policy claim to dominate a stronger one")
val strong = flight_policy()
val weak = ResolvedAssurancePolicyV1.default()
expect(strong.is_at_least_as_strict_as(weak)).to_equal(true)
expect(weak.is_at_least_as_strict_as(strong)).to_equal(false)
```

</details>

### ResolvedAssurancePolicyV2

#### keeps verified out of the frozen V1 identity while preserving it in V2

- keeps verified out of the frozen V1 identity while preserving it in V2
   - Expected: upgraded.strictness equals `AssuranceStrictnessV2.Critical`
   - Expected: upgraded.policy_hash().starts_with("APOLV2-") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps verified out of the frozen V1 identity while preserving it in V2")
expect(AssuranceStrictness.from_name("verified")).to_equal(
    AssuranceStrictness.Critical)
expect(AssuranceStrictnessV2.from_name("verified")).to_equal(
    AssuranceStrictnessV2.Verified)
expect(AssuranceStrictnessV2.Verified.rank()).to_be_greater_than(
    AssuranceStrictnessV2.Critical.rank())
val v1 = flight_policy()
val upgraded = ResolvedAssurancePolicyV2.upgrade_v1(v1)
expect(upgraded.strictness).to_equal(AssuranceStrictnessV2.Critical)
expect(upgraded.policy_hash().starts_with("APOLV2-")).to_equal(true)
```

</details>

### CriticalSymbolSummaryV1

#### starts every lattice at its rejecting bottom for an unanalysed symbol

- starts every lattice at its rejecting bottom for an unanalysed symbol
   - Expected: s.symbol_id equals `sym::foo`
   - Expected: s.allocation_class.name() equals `unknown`
   - Expected: s.blocking.name() equals `unknown`
   - Expected: s.panic_behavior.name() equals `unknown`
   - Expected: s.loop_bound.name() equals `unknown`
   - Expected: s.recursion_bound.name() equals `unknown`
   - Expected: s.proof_status.name() equals `unknown`
   - Expected: s.test_status.name() equals `unknown`
   - Expected: s.backend_lowering.name() equals `unknown`
   - Expected: s.stack_known() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("starts every lattice at its rejecting bottom for an unanalysed symbol")
val s = CriticalSymbolSummaryV1.unknown_for("sym::foo")
expect(s.symbol_id).to_equal("sym::foo")
expect(s.allocation_class.name()).to_equal("unknown")
expect(s.blocking.name()).to_equal("unknown")
expect(s.panic_behavior.name()).to_equal("unknown")
expect(s.loop_bound.name()).to_equal("unknown")
expect(s.recursion_bound.name()).to_equal("unknown")
expect(s.proof_status.name()).to_equal("unknown")
expect(s.test_status.name()).to_equal("unknown")
expect(s.backend_lowering.name()).to_equal("unknown")
expect(s.stack_known()).to_equal(false)
```

</details>

#### rejects an unanalysed symbol rather than passing it

- rejects an unanalysed symbol rather than passing it
   - Expected: s.is_flight_clear() is false
   - Expected: s.failing_rule_ids().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an unanalysed symbol rather than passing it")
val s = CriticalSymbolSummaryV1.unknown_for("sym::foo")
expect(s.is_flight_clear()).to_equal(false)
expect(s.failing_rule_ids().len() > 0).to_equal(true)
```

</details>

#### clears a fully classified symbol

- clears a fully classified symbol
   - Expected: s.failing_rule_ids().len() equals `0`
   - Expected: s.is_flight_clear() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clears a fully classified symbol")
var s = CriticalSymbolSummaryV1.unknown_for("sym::ok")
s.allocation_class = AllocationClass.NoAlloc
s.blocking = BlockingBehavior.NonBlocking
s.panic_behavior = PanicBehavior.NoPanic
s.loop_bound = BoundStatus.Inferred
s.recursion_bound = BoundStatus.NotApplicable
s.stack_bytes = 128
s.proof_status = EvidenceStatus.Proved
s.test_status = EvidenceStatus.Checked
s.backend_lowering = LoweringStatus.Lowered
expect(s.failing_rule_ids().len()).to_equal(0)
expect(s.is_flight_clear()).to_equal(true)
```

</details>

#### names FLT-MEM-001 for an unbounded allocator

- names FLT-MEM-001 for an unbounded allocator
   - Expected: s.failing_rule_ids() contains `FLT-MEM-001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names FLT-MEM-001 for an unbounded allocator")
var s = CriticalSymbolSummaryV1.unknown_for("sym::alloc")
s.allocation_class = AllocationClass.Unbounded
expect(s.failing_rule_ids().contains("FLT-MEM-001")).to_equal(true)
```

</details>

#### names FLT-ABS-002 when indirect targets are enumerated but not closed

- names FLT-ABS-002 when indirect targets are enumerated but not closed
   - Expected: s.failing_rule_ids() contains `FLT-ABS-002`
   - Expected: s.failing_rule_ids() does not contain `FLT-ABS-002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names FLT-ABS-002 when indirect targets are enumerated but not closed")
var s = CriticalSymbolSummaryV1.unknown_for("sym::dyn")
s.dyn_targets = ["a", "b"]
s.dyn_targets_closed = false
expect(s.failing_rule_ids().contains("FLT-ABS-002")).to_equal(true)
s.dyn_targets_closed = true
expect(s.failing_rule_ids().contains("FLT-ABS-002")).to_equal(false)
```

</details>

#### treats a partial backend lowering as not lowered

- treats a partial backend lowering as not lowered
   - Expected: LoweringStatus.Partial.is_flight_acceptable() is false
   - Expected: LoweringStatus.Lowered.is_flight_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a partial backend lowering as not lowered")
expect(LoweringStatus.Partial.is_flight_acceptable()).to_equal(false)
expect(LoweringStatus.Lowered.is_flight_acceptable()).to_equal(true)
```

</details>

#### round-trips the allocation lattice

- round-trips the allocation lattice
   - Expected: AllocationClass.from_name("none").name() equals `none`
   - Expected: AllocationClass.from_name("init_only").name() equals `init_only`
   - Expected: AllocationClass.from_name("bounded_pool").name() equals `bounded_pool`
   - Expected: AllocationClass.from_name("unbounded").name() equals `unbounded`
   - Expected: AllocationClass.from_name("").name() equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips the allocation lattice")
expect(AllocationClass.from_name("none").name()).to_equal("none")
expect(AllocationClass.from_name("init_only").name()).to_equal("init_only")
expect(AllocationClass.from_name("bounded_pool").name()).to_equal("bounded_pool")
expect(AllocationClass.from_name("unbounded").name()).to_equal("unbounded")
expect(AllocationClass.from_name("").name()).to_equal("unknown")
```

</details>

### AssuranceStampV1

#### is deterministic and tagged

- is deterministic and tagged
   - Expected: clean_stamp().stamp_hash() equals `clean_stamp().stamp_hash()`
   - Expected: clean_stamp().stamp_hash().starts_with("ASTMPV1-") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is deterministic and tagged")
expect(clean_stamp().stamp_hash()).to_equal(clean_stamp().stamp_hash())
expect(clean_stamp().stamp_hash().starts_with("ASTMPV1-")).to_equal(true)
```

</details>

#### changes hash when the source hash changes

- changes hash when the source hash changes
   - Expected: s.stamp_hash() == clean_stamp().stamp_hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes hash when the source hash changes")
var s = clean_stamp()
s.source_hash = "src-cccc"
expect(s.stamp_hash() == clean_stamp().stamp_hash()).to_equal(false)
```

</details>

#### admits a clean object for release

- admits a clean object for release
   - Expected: clean_stamp().release_clean() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("admits a clean object for release")
expect(clean_stamp().release_clean()).to_equal(true)
```

</details>

#### fails release on warnings, not just errors

- fails release on warnings, not just errors
   - Expected: s.release_clean() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails release on warnings, not just errors")
var s = clean_stamp()
s.warning_count = 1
expect(s.release_clean()).to_equal(false)
```

</details>

#### fails release on a fabricated weak provider

- fails release on a fabricated weak provider
   - Expected: s.externs.is_closed() is false
   - Expected: s.release_clean() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails release on a fabricated weak provider")
var s = clean_stamp()
s.externs.weak_fabricated = 4023
expect(s.externs.is_closed()).to_equal(false)
expect(s.release_clean()).to_equal(false)
```

</details>

#### fails release on an unbacked extern

- fails release on an unbacked extern
   - Expected: s.release_clean() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails release on an unbacked extern")
var s = clean_stamp()
s.externs.unbacked = 1
expect(s.release_clean()).to_equal(false)
```

</details>

#### links objects only when policy and rule set agree

- links objects only when policy and rule set agree
   - Expected: a.link_compatible_with(b) is true
   - Expected: a.link_compatible_with(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("links objects only when policy and rule set agree")
val a = clean_stamp()
var b = clean_stamp()
b.compiler_hash = "cc-dddd"
b.source_hash = "src-eeee"
expect(a.link_compatible_with(b)).to_equal(true)
b.rule_set_hash = "FLTV1-2"
expect(a.link_compatible_with(b)).to_equal(false)
```

</details>

#### refuses to link across differing policies

- refuses to link across differing policies
   - Expected: a.link_compatible_with(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("refuses to link across differing policies")
val a = clean_stamp()
var b = clean_stamp()
b.policy_hash = ResolvedAssurancePolicyV1.default().policy_hash()
expect(a.link_compatible_with(b)).to_equal(false)
```

</details>

#### treats an empty extern summary as closed

- treats an empty extern summary as closed
   - Expected: ExternProviderSummaryV1.empty().is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats an empty extern summary as closed")
expect(ExternProviderSummaryV1.empty().is_closed()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/assurance_schemas_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ResolvedAssurancePolicyV1, strictness parsing, grade and convention, policy_hash, strictness comparison, ResolvedAssurancePolicyV2, CriticalSymbolSummaryV1, AssuranceStampV1.
- ResolvedAssurancePolicyV1
- strictness parsing
- grade and convention
- policy_hash
- strictness comparison
- ResolvedAssurancePolicyV2
- CriticalSymbolSummaryV1
- AssuranceStampV1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8862f19487bac50c31f55fa1eebe10fa06796b03c5aa097b70601b33ea908903`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8862f19487bac50c31f55fa1eebe10fa06796b03c5aa097b70601b33ea908903`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8862f19487bac50c31f55fa1eebe10fa06796b03c5aa097b70601b33ea908903`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/assurance/assurance_schemas_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/assurance_schemas_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/assurance_schemas_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/assurance_schemas_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/assurance_schemas_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/assurance/assurance_schemas_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the canonical ladder names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/assurance_schemas_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps the frozen deprecated aliases onto canonical names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/assurance_schemas_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails soft to moderate on an unknown or empty name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
