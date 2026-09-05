# struct_init_field_order_fill_spec

> Purpose: Prove that struct-init field ordering and omitted-field fill.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# struct_init_field_order_fill_spec

Purpose: Prove that struct-init field ordering and omitted-field fill.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/struct_init_field_order_fill_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that struct-init field ordering and omitted-field fill.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### struct-init field ordering and omitted-field fill

#### fills omitted leading and trailing fields with zero, not a neighbor's value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fills omitted leading and trailing fields with zero, not a neighbor's value
- Verify: fills omitted leading and trailing fields with zero, not a neighbor's value
   - Expected: t.a equals `0`
   - Expected: t.b equals `5`
   - Expected: t.c equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fills omitted leading and trailing fields with zero, not a neighbor's value")
step("Verify: fills omitted leading and trailing fields with zero, not a neighbor's value")
# @req: REQ-COMP-STRUCT-INIT-FIELD-ORDERING-AND-OMITTED-F-001
val t = Triple(b: 5)
expect(t.a).to_equal(0)
expect(t.b).to_equal(5)
expect(t.c).to_equal(0)
```

</details>

#### fills an omitted middle field with zero

- fills an omitted middle field with zero
- Verify: fills an omitted middle field with zero
   - Expected: t.a equals `1`
   - Expected: t.b equals `0`
   - Expected: t.c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fills an omitted middle field with zero")
step("Verify: fills an omitted middle field with zero")
val t = Triple(a: 1, c: 3)
expect(t.a).to_equal(1)
expect(t.b).to_equal(0)
expect(t.c).to_equal(3)
```

</details>

#### keeps fully positional construction working

- keeps fully positional construction working
- Verify: keeps fully positional construction working
   - Expected: t.a equals `1`
   - Expected: t.b equals `2`
   - Expected: t.c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps fully positional construction working")
step("Verify: keeps fully positional construction working")
val t = Triple(1, 2, 3)
expect(t.a).to_equal(1)
expect(t.b).to_equal(2)
expect(t.c).to_equal(3)
```

</details>

#### keeps reordered named-arg construction working

- keeps reordered named-arg construction working
- Verify: keeps reordered named-arg construction working
   - Expected: t.a equals `1`
   - Expected: t.b equals `2`
   - Expected: t.c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps reordered named-arg construction working")
step("Verify: keeps reordered named-arg construction working")
val t = Triple(c: 3, a: 1, b: 2)
expect(t.a).to_equal(1)
expect(t.b).to_equal(2)
expect(t.c).to_equal(3)
```

</details>

### struct-init field ordering and omitted-field fill (brace form)

#### keeps fully specified brace construction working

- keeps fully specified brace construction working
- Verify: keeps fully specified brace construction working
   - Expected: t.a equals `1`
   - Expected: t.b equals `2`
   - Expected: t.c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps fully specified brace construction working")
step("Verify: keeps fully specified brace construction working")
val t = Triple { a: 1, b: 2, c: 3 }
expect(t.a).to_equal(1)
expect(t.b).to_equal(2)
expect(t.c).to_equal(3)
```

</details>

#### keeps reordered brace-form fields working

- keeps reordered brace-form fields working
- Verify: keeps reordered brace-form fields working
   - Expected: t.a equals `1`
   - Expected: t.b equals `2`
   - Expected: t.c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps reordered brace-form fields working")
step("Verify: keeps reordered brace-form fields working")
val t = Triple { c: 3, a: 1, b: 2 }
expect(t.a).to_equal(1)
expect(t.b).to_equal(2)
expect(t.c).to_equal(3)
```

</details>

#### brace and paren forms produce identical structs for the same omitted-field input

- brace and paren forms produce identical structs for the same omitted-field input
- Verify: brace and paren forms produce identical structs for the same omitted-field input
   - Expected: brace_t.a equals `paren_t.a`
   - Expected: brace_t.b equals `paren_t.b`
   - Expected: brace_t.c equals `paren_t.c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("brace and paren forms produce identical structs for the same omitted-field input")
step("Verify: brace and paren forms produce identical structs for the same omitted-field input")
val brace_t = Triple { b: 5 }
val paren_t = Triple(b: 5)
expect(brace_t.a).to_equal(paren_t.a)
expect(brace_t.b).to_equal(paren_t.b)
expect(brace_t.c).to_equal(paren_t.c)
```

</details>

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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-STRUCT-INIT-FIELD-ORDERING-AND-OMITTED-F-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9e9cd8dce246f3c2228abc6d7ae26baf1e40a709bbeee3f9c656ed6637c9d7ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e9cd8dce246f3c2228abc6d7ae26baf1e40a709bbeee3f9c656ed6637c9d7ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e9cd8dce246f3c2228abc6d7ae26baf1e40a709bbeee3f9c656ed6637c9d7ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/struct_init_field_order_fill_spec.spl
mirror: doc/06_spec/01_unit/compiler/struct_init_field_order_fill_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/struct_init_field_order_fill_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/struct_init_field_order_fill_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/struct_init_field_order_fill_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/struct_init_field_order_fill_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills omitted leading and trailing fields with zero, not a neighbor's value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/struct_init_field_order_fill_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills an omitted middle field with zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/struct_init_field_order_fill_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps fully positional construction working' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
