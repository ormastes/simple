# class_identity_corpus_spec

> Purpose: Prove that class identity corpus — trait/optional/array/param/return + struct control.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# class_identity_corpus_spec

Purpose: Prove that class identity corpus — trait/optional/array/param/return + struct control.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/class_identity_corpus_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that class identity corpus — trait/optional/array/param/return + struct control.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### class identity corpus — trait/optional/array/param/return + struct control

#### TODO(class-identity-contract): trait-typed field snapshots — contract wants 101

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TODO(class-identity-contract): trait-typed field snapshots — contract wants 101
- Verify: TODO(class-identity-contract): trait-typed field snapshots — contract wants 101
   - Expected: th.item.value() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): trait-typed field snapshots — contract wants 101")
step("Verify: TODO(class-identity-contract): trait-typed field snapshots — contract wants 101")
# @req: REQ-COMP-CLASS-IDENTITY-CORPUS-TRAIT-OPTIONAL-ARR-001
val tc = CicTraitCell(n: 100)
val th = CicTraitHolder(item: tc)
tc.n = 101
expect(th.item.value()).to_equal(100)
```

</details>

#### TODO(class-identity-contract): optional class field snapshots — contract wants 111

- TODO(class-identity-contract): optional class field snapshots — contract wants 111
- Verify: TODO(class-identity-contract): optional class field snapshots — contract wants 111
   - Expected: m!.n equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): optional class field snapshots — contract wants 111")
step("Verify: TODO(class-identity-contract): optional class field snapshots — contract wants 111")
val c = CicCell(n: 110)
val oh = CicOptHolder(maybe: c)
c.n = 111
val m = oh.maybe
assert_true(m.?)
expect(m!.n).to_equal(110)
```

</details>

#### TODO(class-identity-contract): array element 1 of 2 snapshots — contract wants 131

- TODO(class-identity-contract): array element 1 of 2 snapshots — contract wants 131
- Verify: TODO(class-identity-contract): array element 1 of 2 snapshots — contract wants 131
   - Expected: b.n equals `130`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): array element 1 of 2 snapshots — contract wants 131")
step("Verify: TODO(class-identity-contract): array element 1 of 2 snapshots — contract wants 131")
val a = CicCell(n: 120)
val b = CicCell(n: 130)
val arr = [a, b]
arr[1].n = 131
expect(b.n).to_equal(130)
```

</details>

#### TODO(class-identity-contract): callee-stored parameter snapshots — contract wants 141

- TODO(class-identity-contract): callee-stored parameter snapshots — contract wants 141
- Verify: TODO(class-identity-contract): callee-stored parameter snapshots — contract wants 141
   - Expected: h.cell.n equals `140`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): callee-stored parameter snapshots — contract wants 141")
step("Verify: TODO(class-identity-contract): callee-stored parameter snapshots — contract wants 141")
val h = CicHolder(cell: CicCell(n: 0))
val c = CicCell(n: 140)
_cic_stash(h, c)
c.n = 141
expect(h.cell.n).to_equal(140)
```

</details>

#### TODO(class-identity-contract): returned class instance snapshots — contract wants 91

- TODO(class-identity-contract): returned class instance snapshots — contract wants 91
- Verify: TODO(class-identity-contract): returned class instance snapshots — contract wants 91
   - Expected: h.cell.n equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TODO(class-identity-contract): returned class instance snapshots — contract wants 91")
step("Verify: TODO(class-identity-contract): returned class instance snapshots — contract wants 91")
val c = _cic_make()
val h = CicHolder(cell: c)
c.n = 91
expect(h.cell.n).to_equal(90)
```

</details>

#### a struct stored in a class field is a VALUE COPY (contract HOLDS on this engine)

- a struct stored in a class field is a VALUE COPY (contract HOLDS on this engine)
- Verify: a struct stored in a class field is a VALUE COPY (contract HOLDS on this engine)
   - Expected: sh.cell.n equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a struct stored in a class field is a VALUE COPY (contract HOLDS on this engine)")
step("Verify: a struct stored in a class field is a VALUE COPY (contract HOLDS on this engine)")
# NEGATIVE CONTROL. This asserts the CONTRACT, not a pinned defect: the
# struct half must never alias. It is GREEN on the interpreter and RED
# on the JIT, which aliases the struct (measured 151). Do not weaken it.
var s = CicStructCell(n: 150)
val sh = CicStructHolder(cell: s)
s.n = 151
expect(sh.cell.n).to_equal(150)
```

</details>

#### mutation through a struct field does not escape to the original

- mutation through a struct field does not escape to the original
- Verify: mutation through a struct field does not escape to the original
   - Expected: s.n equals `160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mutation through a struct field does not escape to the original")
step("Verify: mutation through a struct field does not escape to the original")
var s = CicStructCell(n: 160)
val sh = CicStructHolder(cell: s)
sh.cell.n = 161
expect(s.n).to_equal(160)
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
- `REQ-COMP-CLASS-IDENTITY-CORPUS-TRAIT-OPTIONAL-ARR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6b8421358cbd90c3b52ce1d00fba078e73b025d008204b239a55cd563480496f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b8421358cbd90c3b52ce1d00fba078e73b025d008204b239a55cd563480496f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b8421358cbd90c3b52ce1d00fba078e73b025d008204b239a55cd563480496f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/class_identity_corpus_spec.spl
mirror: doc/06_spec/01_unit/compiler/class_identity_corpus_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/class_identity_corpus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/class_identity_corpus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/class_identity_corpus_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/class_identity_corpus_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TODO(class-identity-contract): trait-typed field snapshots — contract wants 101' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/class_identity_corpus_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TODO(class-identity-contract): optional class field snapshots — contract wants 111' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/class_identity_corpus_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TODO(class-identity-contract): array element 1 of 2 snapshots — contract wants 131' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
