# @manual: primary

> Purpose: Pin option_deep behavior with real computed-value oracles so regressions in the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Pin option_deep behavior with real computed-value oracles so regressions in the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/deep/option_deep_15_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Pin option_deep behavior with real computed-value oracles so regressions in the
stdlib surface this spec covers fail loudly instead of passing vacuously.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-LIB-OPTION-DEEP-7eb6
doc/01_research/local/REQ-LIB-OPTION-DEEP-7eb6.md
doc/03_plan/sys_test/REQ-LIB-OPTION-DEEP-7eb6.md
doc/04_architecture/REQ-LIB-OPTION-DEEP-7eb6.md
doc/05_design/REQ-LIB-OPTION-DEEP-7eb6.md

## Scenarios

### option_deep stdlib behavior oracles

#### array membership and index

- Verify: array membership and index
   - Expected: [3, 1, 2] contains `2`
   - Expected: [3, 1, 2] does not contain `9`
   - Expected: [3, 1, 2].index_of(2) equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-OPTION-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-OPTION-DEEP-7eb6
step("Verify: array membership and index")
# oracle: true/2 — 2 is present at index 2
expect([3, 1, 2].contains(2)).to_equal(true)
expect([3, 1, 2].contains(9)).to_equal(false)
expect([3, 1, 2].index_of(2)).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### array append and len

- Verify: array append and len
   - Expected: arr.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: arr[3] equals `4)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-OPTION-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-OPTION-DEEP-7eb6
step("Verify: array append and len")
# oracle: 4 — append grows the owner list by one and returns it
var arr = [1, 2, 3]
arr.append(4)
expect(arr.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(arr[3]).to_equal(4)  # oracle: pinned constant asserted by this scenario
```

</details>

#### dict read

- Verify: dict read
   - Expected: d.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: d["a"] equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: d.keys().len() equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-OPTION-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-OPTION-DEEP-7eb6
step("Verify: dict read")
# oracle: 2/1/2 — two keys, value lookup, key count
val d = {"a": 1, "b": 2}
expect(d.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(d["a"]).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(d.keys().len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### dict write

- Verify: dict write
   - Expected: d.len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: d["c"] equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-OPTION-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-OPTION-DEEP-7eb6
step("Verify: dict write")
# oracle: 3 — inserting a new key grows the dict by one
val d = {"a": 1, "b": 2}
d["c"] = 3
expect(d.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(d["c"]).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### option map unwrap

- Verify: option map unwrap
   - Expected: o.map(fn (x: i64) -> i64: x * 2) equals `Some(10)`
   - Expected: o.unwrap_or(0) equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: o.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-OPTION-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-OPTION-DEEP-7eb6
step("Verify: option map unwrap")
# oracle: Some(10)/5 — map doubles the payload; unwrap_or yields it
val o = Some(5)
expect(o.map(fn (x: i64) -> i64: x * 2)).to_equal(Some(10))
expect(o.unwrap_or(0)).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(o.is_some()).to_equal(true)
```

</details>

#### option none default

- Verify: option none default
   - Expected: nil.unwrap_or(0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-OPTION-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-OPTION-DEEP-7eb6
step("Verify: option none default")
# oracle: 0 — a nil option falls back to the supplied default
expect(nil.unwrap_or(0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### result ok err

- Verify: result ok err
   - Expected: Ok(7).is_ok() is true
   - Expected: Err("e").is_err() is true
   - Expected: Ok(7).unwrap_or(0) equals `7)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-OPTION-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-OPTION-DEEP-7eb6
step("Verify: result ok err")
# oracle: true/7 — Ok is ok and unwraps; Err is err
expect(Ok(7).is_ok()).to_equal(true)
expect(Err("e").is_err()).to_equal(true)
expect(Ok(7).unwrap_or(0)).to_equal(7)  # oracle: pinned constant asserted by this scenario
```

</details>

#### char code roundtrip

- Verify: char code roundtrip
   - Expected: char_code("a") equals `97)  # oracle: pinned constant asserted by this scenario`
   - Expected: char_from_code(98) equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-OPTION-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-OPTION-DEEP-7eb6
step("Verify: char code roundtrip")
# oracle: 97/"b" — 'a' is codepoint 97; code 98 decodes to 'b'
expect(char_code("a")).to_equal(97)  # oracle: pinned constant asserted by this scenario
expect(char_from_code(98)).to_equal("b")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `240da0b956e03ea67e9723983c39df87c7a828e93720b6fc1b1192d9c81365c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `240da0b956e03ea67e9723983c39df87c7a828e93720b6fc1b1192d9c81365c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `240da0b956e03ea67e9723983c39df87c7a828e93720b6fc1b1192d9c81365c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/deep/option_deep_15_spec.spl
mirror: doc/06_spec/01_unit/std/deep/option_deep_15_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/deep/option_deep_15_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/deep/option_deep_15_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/deep/option_deep_15_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
