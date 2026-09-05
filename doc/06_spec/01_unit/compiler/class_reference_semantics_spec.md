# class_reference_semantics_spec

> Purpose: Prove that class reference semantics (divergence pinned, contract in comments).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# class_reference_semantics_spec

Purpose: Prove that class reference semantics (divergence pinned, contract in comments).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/class_reference_semantics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that class reference semantics (divergence pinned, contract in comments).
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### class reference semantics (divergence pinned, contract in comments)

#### TODO(class-identity-contract): holder field snapshots — contract wants 11

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TODO(class-identity-contract): holder field snapshots — contract wants 11
- Verify: TODO(class-identity-contract): holder field snapshots — contract wants 11
   - Expected: h.cell.n equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): holder field snapshots — contract wants 11")
step("Verify: TODO(class-identity-contract): holder field snapshots — contract wants 11")
# @req: REQ-COMP-CLASS-REFERENCE-SEMANTICS-DIVERGENCE-PIN-001
val c = CrsCell(n: 10)
val h = CrsHolder(cell: c)
c.n = 11
expect(h.cell.n).to_equal(10)
```

</details>

#### TODO(class-identity-contract): field-alias mutation lost — contract wants 21

- TODO(class-identity-contract): field-alias mutation lost — contract wants 21
- Verify: TODO(class-identity-contract): field-alias mutation lost — contract wants 21
   - Expected: c.n equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): field-alias mutation lost — contract wants 21")
step("Verify: TODO(class-identity-contract): field-alias mutation lost — contract wants 21")
val c = CrsCell(n: 20)
val h = CrsHolder(cell: c)
h.cell.n = 21
expect(c.n).to_equal(20)
```

</details>

#### TODO(class-identity-contract): nested field snapshots — contract wants 31

- TODO(class-identity-contract): nested field snapshots — contract wants 31
- Verify: TODO(class-identity-contract): nested field snapshots — contract wants 31
   - Expected: c.n equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): nested field snapshots — contract wants 31")
step("Verify: TODO(class-identity-contract): nested field snapshots — contract wants 31")
val c = CrsCell(n: 30)
val o = CrsOuter(inner: CrsHolder(cell: c))
o.inner.cell.n = 31
expect(c.n).to_equal(30)
```

</details>

#### TODO(class-identity-contract): array element snapshots — contract wants 41

- TODO(class-identity-contract): array element snapshots — contract wants 41
- Verify: TODO(class-identity-contract): array element snapshots — contract wants 41
   - Expected: c.n equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): array element snapshots — contract wants 41")
step("Verify: TODO(class-identity-contract): array element snapshots — contract wants 41")
val c = CrsCell(n: 40)
val arr = [c]
arr[0].n = 41
expect(c.n).to_equal(40)
```

</details>

#### a class parameter aliases the caller's instance (contract HOLDS here)

- a class parameter aliases the caller's instance (contract HOLDS here)
- Verify: a class parameter aliases the caller's instance (contract HOLDS here)
   - Expected: c.n equals `51`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a class parameter aliases the caller's instance (contract HOLDS here)")
step("Verify: a class parameter aliases the caller's instance (contract HOLDS here)")
val c = CrsCell(n: 50)
_crs_bump(c)
expect(c.n).to_equal(51)
```

</details>

#### TODO(class-identity-contract): field re-assign snapshots — contract wants 81

- TODO(class-identity-contract): field re-assign snapshots — contract wants 81
- Verify: TODO(class-identity-contract): field re-assign snapshots — contract wants 81
   - Expected: h.cell.n equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): field re-assign snapshots — contract wants 81")
step("Verify: TODO(class-identity-contract): field re-assign snapshots — contract wants 81")
val h = CrsHolder(cell: CrsCell(n: 70))
val c = CrsCell(n: 80)
h.cell = c
c.n = 81
expect(h.cell.n).to_equal(80)
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
- `REQ-COMP-CLASS-REFERENCE-SEMANTICS-DIVERGENCE-PIN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f6fdebe841ff7b5a8d96f06a08cea9a0162a7176604cc30e42fe254bf447c0d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6fdebe841ff7b5a8d96f06a08cea9a0162a7176604cc30e42fe254bf447c0d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6fdebe841ff7b5a8d96f06a08cea9a0162a7176604cc30e42fe254bf447c0d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/class_reference_semantics_spec.spl
mirror: doc/06_spec/01_unit/compiler/class_reference_semantics_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/class_reference_semantics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/class_reference_semantics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/class_reference_semantics_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/class_reference_semantics_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TODO(class-identity-contract): holder field snapshots — contract wants 11' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/class_reference_semantics_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TODO(class-identity-contract): field-alias mutation lost — contract wants 21' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/class_reference_semantics_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TODO(class-identity-contract): nested field snapshots — contract wants 31' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
