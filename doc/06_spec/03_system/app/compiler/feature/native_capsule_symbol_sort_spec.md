# Native capsule symbol ordering

> Verifies the native capsule symbol sort behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native capsule symbol ordering

Verifies the native capsule symbol sort behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the native capsule symbol sort behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Native capsule symbol sort

#### should order reverse symbols without mutating the caller input

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Deterministic production ordering (expected show, folded, detail, or skip)


- Verify: should order reverse symbols without mutating the caller input
- Create a reverse-ordered native capsule symbol set
- Require ascending output and unchanged value-semantic input
   - Expected: symbol_ids(sorted) equals `[0, 1, 2, 3, 4, 5, 6, 7]`
   - Expected: symbol_ids(input) equals `[7, 6, 5, 4, 3, 2, 1, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-002 REQ-CNSS-003
step("Verify: should order reverse symbols without mutating the caller input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create a reverse-ordered native capsule symbol set")
val input = make_symbols([7, 6, 5, 4, 3, 2, 1, 0])
val sorted = native_capsule_sorted_symbol_ids_v1(input)

step("Require ascending output and unchanged value-semantic input")
expect(symbol_ids(sorted)).to_equal([0, 1, 2, 3, 4, 5, 6, 7])
expect(symbol_ids(input)).to_equal([7, 6, 5, 4, 3, 2, 1, 0])
```

</details>

#### should preserve an already ordered symbol set

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Deterministic production ordering (expected show, folded, detail, or skip)


- Verify: should preserve an already ordered symbol set
- Submit symbols that already satisfy capsule identity order
- Require the exact canonical sequence
   - Expected: symbol_ids(sorted) equals `[0, 1, 2, 3, 4, 5]`
   - Expected: sorted.len() equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-002 REQ-CNSS-003
step("Verify: should preserve an already ordered symbol set")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Submit symbols that already satisfy capsule identity order")
val input = make_symbols([0, 1, 2, 3, 4, 5])
val sorted = native_capsule_sorted_symbol_ids_v1(input)

step("Require the exact canonical sequence")
expect(symbol_ids(sorted)).to_equal([0, 1, 2, 3, 4, 5])
expect(sorted.len()).to_equal(6)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should order mixed negative and duplicate identifiers deterministically

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Deterministic production ordering (expected show, folded, detail, or skip)


- Verify: should order mixed negative and duplicate identifiers deterministically
- Submit non-canonical identifiers without assuming uniqueness
- Require a total ascending order without dropped values
   - Expected: symbol_ids(sorted) equals `[-1, -1, 0, 2, 3, 3]`
   - Expected: sorted.len() equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-001 REQ-CNSS-003
step("Verify: should order mixed negative and duplicate identifiers deterministically")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Submit non-canonical identifiers without assuming uniqueness")
val sorted = native_capsule_sorted_symbol_ids_v1(
    make_symbols([3, -1, 2, 3, 0, -1]))

step("Require a total ascending order without dropped values")
expect(symbol_ids(sorted)).to_equal([-1, -1, 0, 2, 3, 3])
expect(sorted.len()).to_equal(6)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should return an empty result for empty input

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Merge boundary behavior (expected show, folded, detail, or skip)


- Verify: should return an empty result for empty input
- Invoke the production sorter with no symbols
- Require the empty boundary to remain empty
   - Expected: sorted.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: symbol_ids(sorted) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-001 REQ-CNSS-003
step("Verify: should return an empty result for empty input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Invoke the production sorter with no symbols")
val sorted = native_capsule_sorted_symbol_ids_v1([])

step("Require the empty boundary to remain empty")
expect(sorted.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(symbol_ids(sorted)).to_equal([])
```

</details>

#### should preserve a singleton identifier exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Merge boundary behavior (expected show, folded, detail, or skip)


- Verify: should preserve a singleton identifier exactly
- Invoke the production sorter with one symbol
- Require the singleton value and cardinality
   - Expected: sorted.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sorted[0].id equals `41)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-001 REQ-CNSS-003
step("Verify: should preserve a singleton identifier exactly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Invoke the production sorter with one symbol")
val sorted = native_capsule_sorted_symbol_ids_v1(
    [SymbolId(id: 41)])

step("Require the singleton value and cardinality")
expect(sorted.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(sorted[0].id).to_equal(41)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should order a non-power-of-two reverse workload through the partial tail

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Merge boundary behavior (expected show, folded, detail, or skip)


- Verify: should order a non-power-of-two reverse workload through the partial tail
- Create 4097 reverse symbols to exercise the final partial merge run
- Audit every identifier and the complete weighted checksum
   - Expected: audit.code equals `ok`
   - Expected: audit.count equals `4097)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-001 REQ-CNSS-002
step("Verify: should order a non-power-of-two reverse workload through the partial tail")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create 4097 reverse symbols to exercise the final partial merge run")
val sorted = native_capsule_sorted_symbol_ids_v1(
    reverse_symbols(4097))

step("Audit every identifier and the complete weighted checksum")
val audit = audit_expected_sequence(sorted, 4097)
expect(audit.code).to_equal("ok")
expect(audit.count).to_equal(4097)  # oracle: pinned constant asserted by this scenario
expect(audit.checksum).to_be_greater_than(0)
```

</details>

#### should accept a complete canonical result with an exact checksum

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Fail-closed result auditing (expected show, folded, detail, or skip)


- Verify: should accept a complete canonical result with an exact checksum
- Sort one complete canonical fixture
- Require the auditor to accept every position
   - Expected: audit.code equals `ok`
   - Expected: audit.count equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: audit.checksum equals `204)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-001 REQ-CNSS-002
step("Verify: should accept a complete canonical result with an exact checksum")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Sort one complete canonical fixture")
val sorted = native_capsule_sorted_symbol_ids_v1(
    reverse_symbols(8))

step("Require the auditor to accept every position")
val audit = audit_expected_sequence(sorted, 8)
expect(audit.code).to_equal("ok")
expect(audit.count).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(audit.checksum).to_equal(204)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject a result with missing symbols

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Fail-closed result auditing (expected show, folded, detail, or skip)


- Verify: should reject a result with missing symbols
- Construct a result whose cardinality is smaller than declared
- Require an exact fail-closed length error
   - Expected: audit.code equals `length-mismatch`
   - Expected: audit.count equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: audit.checksum equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-001 REQ-CNSS-002
step("Verify: should reject a result with missing symbols")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Construct a result whose cardinality is smaller than declared")
val incomplete = make_symbols([0, 1, 2])

step("Require an exact fail-closed length error")
val audit = audit_expected_sequence(incomplete, 4)
expect(audit.code).to_equal("length-mismatch")
expect(audit.count).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(audit.checksum).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject an interior duplicate that endpoint checks would miss

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Fail-closed result auditing (expected show, folded, detail, or skip)


- Verify: should reject an interior duplicate that endpoint checks would miss
- Corrupt one interior position while retaining the expected endpoints
- Require the auditor to name the first mismatched position
   - Expected: audit.code equals `id-mismatch:2`
   - Expected: audit.count equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: audit.checksum equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CNSS-001 REQ-CNSS-002 REQ-CNSS-003
step("Verify: should reject an interior duplicate that endpoint checks would miss")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Corrupt one interior position while retaining the expected endpoints")
val corrupted = make_symbols([0, 1, 1, 3])

step("Require the auditor to name the first mismatched position")
val audit = audit_expected_sequence(corrupted, 4)
expect(audit.code).to_equal("id-mismatch:2")
expect(audit.count).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(audit.checksum).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ccdf41540a4755598b46c561daf4b5475832af37463bee7125b09a8671ad1bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ccdf41540a4755598b46c561daf4b5475832af37463bee7125b09a8671ad1bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ccdf41540a4755598b46c561daf4b5475832af37463bee7125b09a8671ad1bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should order reverse symbols without mutating the caller input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve an already ordered symbol set' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should order mixed negative and duplicate identifiers deterministically' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:124:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return an empty result for empty input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:137:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve a singleton identifier exactly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:151:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should order a non-power-of-two reverse workload through the partial tail' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
