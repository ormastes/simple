# Enum Lowering End To End Unit Spec

> Purpose: Prove that enum lowering end to end.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Lowering End To End Unit Spec

Purpose: Prove that enum lowering end to end.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/enum_lowering_end_to_end_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that enum lowering end to end.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### enum lowering end to end

#### lowers a decorated enum to a non-nil HirEnum (reproduce: positional ParserEnum destructure)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers a decorated enum to a non-nil HirEnum (reproduce: positional ParserEnum destructure)
- Verify: lowers a decorated enum to a non-nil HirEnum (reproduce: positional ParserEnum destructure)
   - Expected: hm.enums.len() equals `1`
   - Expected: e.name equals `Color`
   - Expected: e.variants.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a decorated enum to a non-nil HirEnum (reproduce: positional ParserEnum destructure)")
step("Verify: lowers a decorated enum to a non-nil HirEnum (reproduce: positional ParserEnum destructure)")
# @req: REQ-COMPILER-HIR-001
val hm = lower(CLOSED_SRC)
expect(hm.enums.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val e = only_enum(hm)
expect(e.name).to_equal("Color")
expect(e.variants.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### carries @closed onto HirEnum.attributes through real lowering

- carries @closed onto HirEnum.attributes through real lowering
- Verify: carries @closed onto HirEnum.attributes through real lowering
   - Expected: hir_enum_has_attribute(e, "closed") is true
   - Expected: hir_enum_has_attribute(e, "evolving") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries @closed onto HirEnum.attributes through real lowering")
step("Verify: carries @closed onto HirEnum.attributes through real lowering")
val e = only_enum(lower(CLOSED_SRC))
expect(hir_enum_has_attribute(e, "closed")).to_equal(true)
expect(hir_enum_has_attribute(e, "evolving")).to_equal(false)
```

</details>

#### carries @evolving(...) with its raw argument text

- carries @evolving(...) with its raw argument text
- Verify: carries @evolving(...) with its raw argument text
   - Expected: hir_enum_has_attribute(e, "evolving") is true
   - Expected: hir_enum_attribute_args(e, "evolving") equals `repr:u16,unknown:Unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries @evolving(...) with its raw argument text")
step("Verify: carries @evolving(...) with its raw argument text")
val e = only_enum(lower(EVOLVING_SRC))
expect(hir_enum_has_attribute(e, "evolving")).to_equal(true)
expect(hir_enum_attribute_args(e, "evolving")).to_equal("repr:u16,unknown:Unknown")
```

</details>

#### lowers unit variants with an EMPTY payload (reproduce: 620-element garbage Tuple)

- lowers unit variants with an EMPTY payload (reproduce: 620-element garbage Tuple)
- Verify: lowers unit variants with an EMPTY payload (reproduce: 620-element garbage Tuple)
   - Expected: tuple_arity(e, "Red") equals `0`
   - Expected: tuple_arity(e, "Green") equals `0`
   - Expected: tuple_arity(e, "Blue") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers unit variants with an EMPTY payload (reproduce: 620-element garbage Tuple)")
step("Verify: lowers unit variants with an EMPTY payload (reproduce: 620-element garbage Tuple)")
val e = only_enum(lower(CLOSED_SRC))
expect(tuple_arity(e, "Red")).to_equal(0)
expect(tuple_arity(e, "Green")).to_equal(0)
expect(tuple_arity(e, "Blue")).to_equal(0)
```

</details>

#### neighbor: an undecorated enum lowers with zero attributes

- neighbor: an undecorated enum lowers with zero attributes
- Verify: neighbor: an undecorated enum lowers with zero attributes
   - Expected: e.name equals `Plain`
   - Expected: e.attributes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("neighbor: an undecorated enum lowers with zero attributes")
step("Verify: neighbor: an undecorated enum lowers with zero attributes")
val e = only_enum(lower("enum Plain:\n    A\n    B\n"))
expect(e.name).to_equal("Plain")
expect(e.attributes.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### neighbor: discriminants survive lowering alongside attributes

- neighbor: discriminants survive lowering alongside attributes
- Verify: neighbor: discriminants survive lowering alongside attributes
   - Expected: with_disc equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("neighbor: discriminants survive lowering alongside attributes")
step("Verify: neighbor: discriminants survive lowering alongside attributes")
val e = only_enum(lower(EVOLVING_SRC))
var with_disc = 0
for v in e.variants:
    if v.has_discriminant:
        with_disc = with_disc + 1
expect(with_disc).to_equal(2)  # oracle: 2 — named expected value from the requirement
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

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-HIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `70664547d3f2906e8f9b1c78d886046c82d50ac5c22673ef6ea2b28d7008ded1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70664547d3f2906e8f9b1c78d886046c82d50ac5c22673ef6ea2b28d7008ded1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70664547d3f2906e8f9b1c78d886046c82d50ac5c22673ef6ea2b28d7008ded1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/enum_lowering_end_to_end_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/enum_lowering_end_to_end_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/enum_lowering_end_to_end_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/enum_lowering_end_to_end_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/enum_lowering_end_to_end_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/enum_lowering_end_to_end_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a decorated enum to a non-nil HirEnum (reproduce: positional ParserEnum destructure)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/enum_lowering_end_to_end_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries @closed onto HirEnum.attributes through real lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/enum_lowering_end_to_end_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries @evolving(...) with its raw argument text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
