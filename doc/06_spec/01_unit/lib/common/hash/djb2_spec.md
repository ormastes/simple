# DJB2-compatible signed 32-bit text hash

> Purpose: Prove that djb2_hash_text.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DJB2-compatible signed 32-bit text hash

Purpose: Prove that djb2_hash_text.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hash/djb2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that djb2_hash_text.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### djb2_hash_text

#### matches empty and short ASCII vectors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches empty and short ASCII vectors
- Verify: matches empty and short ASCII vectors
   - Expected: djb2_hash_text("") equals `0`
   - Expected: djb2_hash_text("a") equals `97`
   - Expected: djb2_hash_text("ab") equals `3105`
   - Expected: djb2_hash_text("abc") equals `96354`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches empty and short ASCII vectors")
step("Verify: matches empty and short ASCII vectors")
# @req: REQ-LIB-COMMON-001
expect(djb2_hash_text("")).to_equal(0)
expect(djb2_hash_text("a")).to_equal(97)
expect(djb2_hash_text("ab")).to_equal(3105)
expect(djb2_hash_text("abc")).to_equal(96354)
```

</details>

#### matches a common word vector

- matches a common word vector
- Verify: matches a common word vector
   - Expected: djb2_hash_text("hello") equals `99162322`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches a common word vector")
step("Verify: matches a common word vector")
expect(djb2_hash_text("hello")).to_equal(99162322)
```

</details>

#### wraps as signed 32-bit

- wraps as signed 32-bit
- Verify: wraps as signed 32-bit
   - Expected: djb2_hash_text("zzzzzzzz") equals `-1910022912`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wraps as signed 32-bit")
step("Verify: wraps as signed 32-bit")
expect(djb2_hash_text("zzzzzzzz")).to_equal(-1910022912)
```

</details>

#### hashes supplementary characters as UTF-16 code units

- hashes supplementary characters as UTF-16 code units
- Verify: hashes supplementary characters as UTF-16 code units
   - Expected: djb2_hash_text("😀") equals `1772899`
   - Expected: djb2_hash_text("a😀b") equals `57849694`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes supplementary characters as UTF-16 code units")
step("Verify: hashes supplementary characters as UTF-16 code units")
expect(djb2_hash_text("😀")).to_equal(1772899)
expect(djb2_hash_text("a😀b")).to_equal(57849694)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c5e9f48346648fb3c2a41fdb569f84bdf1bb8915f0d4eedd745ebb4f4d38b9ae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5e9f48346648fb3c2a41fdb569f84bdf1bb8915f0d4eedd745ebb4f4d38b9ae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5e9f48346648fb3c2a41fdb569f84bdf1bb8915f0d4eedd745ebb4f4d38b9ae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/hash/djb2_spec.spl
mirror: doc/06_spec/01_unit/lib/common/hash/djb2_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/hash/djb2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/hash/djb2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/hash/djb2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/hash/djb2_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches empty and short ASCII vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/hash/djb2_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches a common word vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/hash/djb2_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps as signed 32-bit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
