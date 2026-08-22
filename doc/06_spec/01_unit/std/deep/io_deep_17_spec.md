# @manual: primary

> Purpose: Pin io_deep behavior with real computed-value oracles so regressions in the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Pin io_deep behavior with real computed-value oracles so regressions in the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/deep/io_deep_17_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Pin io_deep behavior with real computed-value oracles so regressions in the
stdlib surface this spec covers fail loudly instead of passing vacuously.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-LIB-IO-DEEP-37bc
doc/01_research/local/REQ-LIB-IO-DEEP-37bc.md
doc/03_plan/sys_test/REQ-LIB-IO-DEEP-37bc.md
doc/04_architecture/REQ-LIB-IO-DEEP-37bc.md
doc/05_design/REQ-LIB-IO-DEEP-37bc.md

## Scenarios

### io_deep stdlib behavior oracles

#### dict write

- Verify: dict write
   - Expected: d.len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: d["c"] equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IO-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-IO-DEEP-37bc
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
# @req: REQ-LIB-IO-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-IO-DEEP-37bc
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
# @req: REQ-LIB-IO-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-IO-DEEP-37bc
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
# @req: REQ-LIB-IO-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-IO-DEEP-37bc
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
# @req: REQ-LIB-IO-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-IO-DEEP-37bc
step("Verify: char code roundtrip")
# oracle: 97/"b" — 'a' is codepoint 97; code 98 decodes to 'b'
expect(char_code("a")).to_equal(97)  # oracle: pinned constant asserted by this scenario
expect(char_from_code(98)).to_equal("b")
```

</details>

<details>
<summary>Advanced: loop accumulates in order</summary>

#### loop accumulates in order

- Verify: loop accumulates in order
   - Expected: sum equals `10)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IO-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-IO-DEEP-37bc
step("Verify: loop accumulates in order")
# oracle: 10 — sum of 0..5 exclusive end
var sum = 0
for i in 0..5:
    sum = sum + i
expect(sum).to_equal(10)  # oracle: pinned constant asserted by this scenario
```

</details>


</details>

#### match destructures Some

- Verify: match destructures Some
   - Expected: x equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IO-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-IO-DEEP-37bc
step("Verify: match destructures Some")
# oracle: 1 — the Some arm binds the payload
match Some(1):
    Some(x):
        expect(x).to_equal(1)  # oracle: pinned constant asserted by this scenario
    nil:
        expect(false).to_equal(true)
```

</details>

#### string length and emptiness

- Verify: string length and emptiness
   - Expected: "test".len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: "".len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: "".is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IO-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-IO-DEEP-37bc
step("Verify: string length and emptiness")
# oracle: 4/0 — len counts chars; only the empty string is empty
expect("test".len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect("".len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect("".is_empty()).to_equal(true)
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

- Canonical SPipe generation for source `53abfc47d0c9903a103aec278bbdcc6a23cd84329f94a04897dcf4be98d49ded`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53abfc47d0c9903a103aec278bbdcc6a23cd84329f94a04897dcf4be98d49ded`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53abfc47d0c9903a103aec278bbdcc6a23cd84329f94a04897dcf4be98d49ded`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/deep/io_deep_17_spec.spl
mirror: doc/06_spec/01_unit/std/deep/io_deep_17_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/deep/io_deep_17_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/deep/io_deep_17_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/deep/io_deep_17_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
