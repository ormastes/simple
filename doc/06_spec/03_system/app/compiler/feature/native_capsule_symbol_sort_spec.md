# Native capsule symbol ordering

> This system contract exercises the deterministic symbol ordering used by

**Audience:** compiler maintainers reviewing frozen native-capsule identity
generation and operators qualifying a future self-hosted CLI.

**Executable source:**
`test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl`

## Purpose and claim boundary

This system contract exercises the deterministic symbol ordering used by

The Rust seed is prohibited. The admitted pure-Simple Stage 2 compiler used by
the performance lane supports only `compile` and `native-build`, so it cannot
certify this SSpec runner or its documentation pipeline.

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This system contract exercises the deterministic symbol ordering used by
frozen native-capsule identity generation. It covers normal ordering, boundary
shapes that reach partial merge tails, and a fail-closed result auditor. It
does not substitute timing thresholds for the retained performance report.

## Scenarios

Requirement: REQ-CNSS-001.

1. Create a reverse-ordered native-capsule symbol set.
2. Invoke the production sorter.
3. Require IDs `0..7` in ascending order.
4. Require the original input to remain `7..0`.

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Deterministic production ordering (expected show, folded, detail, or skip)


- should order reverse symbols without mutating the caller input
- Create a reverse-ordered native capsule symbol set
- Require ascending output and unchanged value-semantic input
   - Expected: symbol_ids(sorted) equals `[0, 1, 2, 3, 4, 5, 6, 7]`
   - Expected: symbol_ids(input) equals `[7, 6, 5, 4, 3, 2, 1, 0]`

1. Submit IDs `0..5` in canonical order.
2. Invoke the production sorter.
3. Require the identical six-element sequence.

### Should order mixed negative and duplicate identifiers deterministically

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should order reverse symbols without mutating the caller input")
step("Create a reverse-ordered native capsule symbol set")
val input = make_symbols([7, 6, 5, 4, 3, 2, 1, 0])
val sorted = native_capsule_sorted_symbol_ids_v1(input)

Requirement: REQ-CNSS-002.

1. Invoke the sorter with no symbols.
2. Require zero output values.

### Should preserve a singleton identifier exactly

Requirement: REQ-CNSS-002.

1. Invoke the sorter with `SymbolId(41)`.
2. Require one output whose ID remains `41`.

### Should order a non-power-of-two reverse workload through the partial tail

Requirements: REQ-CNSS-002 and NFR-CNSS-001.

1. Generate 4,097 reverse-ordered IDs.
2. Invoke the production sorter so the final merge pass has a partial tail.
3. Audit every output position, exact cardinality, and a positive weighted
   checksum.
4. Require audit code `ok`.

## Fail-closed result auditing

### Should accept a complete canonical result with an exact checksum

Requirement: REQ-CNSS-003.

1. Sort eight reverse-ordered IDs.
2. Audit every position.
3. Require code `ok`, count `8`, and weighted checksum `204`.

### Should reject a result with missing symbols

Requirement: REQ-CNSS-003.

1. Present three IDs while declaring four expected values.
2. Require `length-mismatch`, observed count `3`, and checksum `-1`.

### Should reject interior corruption that endpoint checks would miss

Requirement: REQ-CNSS-003.

1. Present `[0, 1, 1, 3]`, retaining the expected endpoints while corrupting
   the interior.
2. Require `id-mismatch:2`, count `4`, and checksum `-1`.

## Qualified operator commands

```text
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --mode=native
bin/simple spipe-docgen test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --baseline
```

</details>

#### should preserve an already ordered symbol set

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Deterministic production ordering (expected show, folded, detail, or skip)


- should preserve an already ordered symbol set
- Submit symbols that already satisfy capsule identity order
- Require the exact canonical sequence
   - Expected: symbol_ids(sorted) equals `[0, 1, 2, 3, 4, 5]`
   - Expected: sorted.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve an already ordered symbol set")
step("Submit symbols that already satisfy capsule identity order")
val input = make_symbols([0, 1, 2, 3, 4, 5])
val sorted = native_capsule_sorted_symbol_ids_v1(input)

step("Require the exact canonical sequence")
expect(symbol_ids(sorted)).to_equal([0, 1, 2, 3, 4, 5])
expect(sorted.len()).to_equal(6)
```

</details>

#### should order mixed negative and duplicate identifiers deterministically

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Deterministic production ordering (expected show, folded, detail, or skip)


- should order mixed negative and duplicate identifiers deterministically
- Submit non-canonical identifiers without assuming uniqueness
- Require a total ascending order without dropped values
   - Expected: symbol_ids(sorted) equals `[-1, -1, 0, 2, 3, 3]`
   - Expected: sorted.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should order mixed negative and duplicate identifiers deterministically")
step("Submit non-canonical identifiers without assuming uniqueness")
val sorted = native_capsule_sorted_symbol_ids_v1(
    make_symbols([3, -1, 2, 3, 0, -1]))

step("Require a total ascending order without dropped values")
expect(symbol_ids(sorted)).to_equal([-1, -1, 0, 2, 3, 3])
expect(sorted.len()).to_equal(6)
```

</details>

#### should return an empty result for empty input

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Merge boundary behavior (expected show, folded, detail, or skip)


- should return an empty result for empty input
- Invoke the production sorter with no symbols
- Require the empty boundary to remain empty
   - Expected: sorted.len() equals `0`
   - Expected: symbol_ids(sorted) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return an empty result for empty input")
step("Invoke the production sorter with no symbols")
val sorted = native_capsule_sorted_symbol_ids_v1([])

step("Require the empty boundary to remain empty")
expect(sorted.len()).to_equal(0)
expect(symbol_ids(sorted)).to_equal([])
```

</details>

#### should preserve a singleton identifier exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Merge boundary behavior (expected show, folded, detail, or skip)


- should preserve a singleton identifier exactly
- Invoke the production sorter with one symbol
- Require the singleton value and cardinality
   - Expected: sorted.len() equals `1`
   - Expected: sorted[0].id equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve a singleton identifier exactly")
step("Invoke the production sorter with one symbol")
val sorted = native_capsule_sorted_symbol_ids_v1(
    [SymbolId(id: 41)])

step("Require the singleton value and cardinality")
expect(sorted.len()).to_equal(1)
expect(sorted[0].id).to_equal(41)
```

</details>

#### should order a non-power-of-two reverse workload through the partial tail

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Merge boundary behavior (expected show, folded, detail, or skip)


- should order a non-power-of-two reverse workload through the partial tail
- Create 4097 reverse symbols to exercise the final partial merge run
- Audit every identifier and the complete weighted checksum
   - Expected: audit.code equals `ok`
   - Expected: audit.count equals `4097`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should order a non-power-of-two reverse workload through the partial tail")
step("Create 4097 reverse symbols to exercise the final partial merge run")
val sorted = native_capsule_sorted_symbol_ids_v1(
    reverse_symbols(4097))

step("Audit every identifier and the complete weighted checksum")
val audit = audit_expected_sequence(sorted, 4097)
expect(audit.code).to_equal("ok")
expect(audit.count).to_equal(4097)
expect(audit.checksum).to_be_greater_than(0)
```

</details>

#### should accept a complete canonical result with an exact checksum

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Fail-closed result auditing (expected show, folded, detail, or skip)


- should accept a complete canonical result with an exact checksum
- Sort one complete canonical fixture
- Require the auditor to accept every position
   - Expected: audit.code equals `ok`
   - Expected: audit.count equals `8`
   - Expected: audit.checksum equals `204`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept a complete canonical result with an exact checksum")
step("Sort one complete canonical fixture")
val sorted = native_capsule_sorted_symbol_ids_v1(
    reverse_symbols(8))

step("Require the auditor to accept every position")
val audit = audit_expected_sequence(sorted, 8)
expect(audit.code).to_equal("ok")
expect(audit.count).to_equal(8)
expect(audit.checksum).to_equal(204)
```

</details>

#### should reject a result with missing symbols

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Fail-closed result auditing (expected show, folded, detail, or skip)


- should reject a result with missing symbols
- Construct a result whose cardinality is smaller than declared
- Require an exact fail-closed length error
   - Expected: audit.code equals `length-mismatch`
   - Expected: audit.count equals `3`
   - Expected: audit.checksum equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a result with missing symbols")
step("Construct a result whose cardinality is smaller than declared")
val incomplete = make_symbols([0, 1, 2])

step("Require an exact fail-closed length error")
val audit = audit_expected_sequence(incomplete, 4)
expect(audit.code).to_equal("length-mismatch")
expect(audit.count).to_equal(3)
expect(audit.checksum).to_equal(-1)
```

</details>

#### should reject an interior duplicate that endpoint checks would miss

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Fail-closed result auditing (expected show, folded, detail, or skip)


- should reject an interior duplicate that endpoint checks would miss
- Corrupt one interior position while retaining the expected endpoints
- Require the auditor to name the first mismatched position
   - Expected: audit.code equals `id-mismatch:2`
   - Expected: audit.count equals `4`
   - Expected: audit.checksum equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an interior duplicate that endpoint checks would miss")
step("Corrupt one interior position while retaining the expected endpoints")
val corrupted = make_symbols([0, 1, 1, 3])

step("Require the auditor to name the first mismatched position")
val audit = audit_expected_sequence(corrupted, 4)
expect(audit.code).to_equal("id-mismatch:2")
expect(audit.count).to_equal(4)
expect(audit.checksum).to_equal(-1)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `25ae0fc6edb7d869f45bddd2b3d835373308fe648bc5af10a070c8941af3d652`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25ae0fc6edb7d869f45bddd2b3d835373308fe648bc5af10a070c8941af3d652`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25ae0fc6edb7d869f45bddd2b3d835373308fe648bc5af10a070c8941af3d652`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should order reverse symbols without mutating the caller input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should order reverse symbols without mutating the caller input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve an already ordered symbol set' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve an already ordered symbol set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should order mixed negative and duplicate identifiers deterministically' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should order mixed negative and duplicate identifiers deterministically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return an empty result for empty input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:122:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve a singleton identifier exactly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl:135:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should order a non-power-of-two reverse workload through the partial tail' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
