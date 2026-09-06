# global_var_type_spec

> Purpose: Prove that Module-level typed variable declarations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# global_var_type_spec

Purpose: Prove that Module-level typed variable declarations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/global_var_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Module-level typed variable declarations.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Module-level typed variable declarations

#### var g_addr: u64 preserves integer addition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- var g_addr: u64 preserves integer addition
- Verify: var g_addr: u64 preserves integer addition
   - Expected: compute_address() equals `0xFD001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("var g_addr: u64 preserves integer addition")
step("Verify: var g_addr: u64 preserves integer addition")
# @req: REQ-COMP-MODULE-LEVEL-TYPED-VARIABLE-DECLARATIONS-001
expect(compute_address()).to_equal(0xFD001000)
```

</details>

#### var g_count: u64 preserves integer arithmetic

- var g_count: u64 preserves integer arithmetic
- Verify: var g_count: u64 preserves integer arithmetic
   - Expected: increment_count() equals `101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("var g_count: u64 preserves integer arithmetic")
step("Verify: var g_count: u64 preserves integer arithmetic")
expect(increment_count()).to_equal(101)
```

</details>

#### val g_offset: u64 preserves value

- val g_offset: u64 preserves value
- Verify: val g_offset: u64 preserves value
   - Expected: g_offset equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("val g_offset: u64 preserves value")
step("Verify: val g_offset: u64 preserves value")
expect(g_offset).to_equal(0x1000)
```

</details>

#### var g_signed: i64 supports negative values

- var g_signed: i64 supports negative values
- Verify: var g_signed: i64 supports negative values
   - Expected: signed_add() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("var g_signed: i64 supports negative values")
step("Verify: var g_signed: i64 supports negative values")
expect(signed_add()).to_equal(10)
```

</details>

#### module-level var can be mutated

- module-level var can be mutated
- Verify: module-level var can be mutated
   - Expected: g_count equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module-level var can be mutated")
step("Verify: module-level var can be mutated")
g_count = 200
expect(g_count).to_equal(200)
g_count = 100
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
- `REQ-COMP-MODULE-LEVEL-TYPED-VARIABLE-DECLARATIONS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `383ae8482465723d76bd569b44917861ce6a5e8edc36bb2a4fcd9aa77265440d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `383ae8482465723d76bd569b44917861ce6a5e8edc36bb2a4fcd9aa77265440d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `383ae8482465723d76bd569b44917861ce6a5e8edc36bb2a4fcd9aa77265440d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/global_var_type_spec.spl
mirror: doc/06_spec/unit/compiler/global_var_type_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/global_var_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/global_var_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/global_var_type_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/global_var_type_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var g_addr: u64 preserves integer addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/global_var_type_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var g_count: u64 preserves integer arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/global_var_type_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'val g_offset: u64 preserves value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
