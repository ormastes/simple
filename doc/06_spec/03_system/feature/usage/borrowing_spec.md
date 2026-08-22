# @manual: primary

> Purpose: Prove that Borrowing and Reference Capabilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Borrowing and Reference Capabilities.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Management |
| Status | In Progress |
| Source | `test/03_system/feature/usage/borrowing_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Borrowing and Reference Capabilities.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-FEATURE-BORROWING-001
doc/01_research/feature/REQ-FEATURE-BORROWING-001.md
doc/03_plan/feature/REQ-FEATURE-BORROWING-001.md
doc/04_architecture/feature/REQ-FEATURE-BORROWING-001.md
doc/05_design/feature/REQ-FEATURE-BORROWING-001.md

## Scenarios

### Borrowing and Reference Capabilities

#### Immutable references

#### allows multiple immutable reads of one value

- Verify: two helpers read the same array without interference
   - Expected: first_of(xs) equals `7`
   - Expected: count_of(xs) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-BORROWING-001
step("Verify: two helpers read the same array without interference")
val xs = [7, 8, 9]
expect(first_of(xs)).to_equal(7)
expect(count_of(xs)).to_equal(3)
```

</details>

#### Mutable references

#### observes a mutation applied through a helper

- Verify: a helper-applied mutation is visible to the caller
   - Expected: counter equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-BORROWING-001
step("Verify: a helper-applied mutation is visible to the caller")
var counter = 0
counter = bump(counter)
counter = bump(counter)
expect(counter).to_equal(2)
```

</details>

#### Ownership transfer

#### moves a value through a consuming function call

- Verify: the callee receives the whole value and returns its length
   - Expected: consume_len("borrow-me") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-BORROWING-001
step("Verify: the callee receives the whole value and returns its length")
expect(consume_len("borrow-me")).to_equal(9)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e628831cac007f6556538377369c8f613f8930adecd214ee628fba2b0c16f7ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e628831cac007f6556538377369c8f613f8930adecd214ee628fba2b0c16f7ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e628831cac007f6556538377369c8f613f8930adecd214ee628fba2b0c16f7ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/feature/usage/borrowing_spec.spl
mirror: doc/06_spec/03_system/feature/usage/borrowing_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/borrowing_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/feature/usage/borrowing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/borrowing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/borrowing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/borrowing_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows multiple immutable reads of one value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/borrowing_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'observes a mutation applied through a helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/borrowing_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'moves a value through a consuming function call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
