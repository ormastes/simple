# @manual: primary

> Purpose: Pin json_deep behavior with real computed-value oracles so regressions in the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Pin json_deep behavior with real computed-value oracles so regressions in the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/deep/json_deep_15_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Pin json_deep behavior with real computed-value oracles so regressions in the
stdlib surface this spec covers fail loudly instead of passing vacuously.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-LIB-JSON-DEEP-01b6
doc/01_research/local/REQ-LIB-JSON-DEEP-01b6.md
doc/03_plan/sys_test/REQ-LIB-JSON-DEEP-01b6.md
doc/04_architecture/REQ-LIB-JSON-DEEP-01b6.md
doc/05_design/REQ-LIB-JSON-DEEP-01b6.md

## Scenarios

### json_deep stdlib behavior oracles

#### text replace

- Verify: text replace
   - Expected: "hello".replace("l", "L") equals `heLLo`
   - Expected: "aaa".replace("a", "b") equals `bbb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-JSON-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-JSON-DEEP-01b6
step("Verify: text replace")
# oracle: "heLLo" — every 'l' replaced by 'L'
expect("hello".replace("l", "L")).to_equal("heLLo")
expect("aaa".replace("a", "b")).to_equal("bbb")
```

</details>

#### text concat slice reverse

- Verify: text concat slice reverse
   - Expected: "abc" + "def" equals `abcdef`
   - Expected: "abc".slice(1) equals `bc`
   - Expected: "abc".reverse() equals `cba`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-JSON-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-JSON-DEEP-01b6
step("Verify: text concat slice reverse")
# oracle: "abcdef"/"bc"/"cba" — concat, slice from index 1, reverse
expect("abc" + "def").to_equal("abcdef")
expect("abc".slice(1)).to_equal("bc")
expect("abc".reverse()).to_equal("cba")
```

</details>

#### array sort

- Verify: array sort
   - Expected: [3, 1, 2].sorted() equals `[1, 2, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-JSON-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-JSON-DEEP-01b6
step("Verify: array sort")
# oracle: [1, 2, 3] — sorted() returns ascending order
expect([3, 1, 2].sorted()).to_equal([1, 2, 3])
```

</details>

#### array map filter

- Verify: array map filter
   - Expected: [3, 1, 2].map(fn (x: i64) -> i64: x + 1) equals `[4, 2, 3]`
   - Expected: [3, 1, 2].filter(fn (x: i64) -> bool: x > 1) equals `[3, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-JSON-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-JSON-DEEP-01b6
step("Verify: array map filter")
# oracle: [4, 2, 3] — each element +1; [3, 2] — elements > 1 in order
expect([3, 1, 2].map(fn (x: i64) -> i64: x + 1)).to_equal([4, 2, 3])
expect([3, 1, 2].filter(fn (x: i64) -> bool: x > 1)).to_equal([3, 2])
```

</details>

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
# @req: REQ-LIB-JSON-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-JSON-DEEP-01b6
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
# @req: REQ-LIB-JSON-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-JSON-DEEP-01b6
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
# @req: REQ-LIB-JSON-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-JSON-DEEP-01b6
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
# @req: REQ-LIB-JSON-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-JSON-DEEP-01b6
step("Verify: dict write")
# oracle: 3 — inserting a new key grows the dict by one
val d = {"a": 1, "b": 2}
d["c"] = 3
expect(d.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(d["c"]).to_equal(3)  # oracle: pinned constant asserted by this scenario
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

- Canonical SPipe generation for source `1c5063154afddfb0a569f52585f0685ee11620a306befee8d33d6430900560da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c5063154afddfb0a569f52585f0685ee11620a306befee8d33d6430900560da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c5063154afddfb0a569f52585f0685ee11620a306befee8d33d6430900560da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/deep/json_deep_15_spec.spl
mirror: doc/06_spec/01_unit/std/deep/json_deep_15_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/deep/json_deep_15_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/deep/json_deep_15_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/deep/json_deep_15_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
