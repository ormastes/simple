# @manual: primary

> Purpose: Pin error_deep behavior with real computed-value oracles so regressions in the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Pin error_deep behavior with real computed-value oracles so regressions in the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/deep/error_deep_12_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Pin error_deep behavior with real computed-value oracles so regressions in the
stdlib surface this spec covers fail loudly instead of passing vacuously.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-LIB-ERROR-DEEP-4aeb
doc/01_research/local/REQ-LIB-ERROR-DEEP-4aeb.md
doc/03_plan/sys_test/REQ-LIB-ERROR-DEEP-4aeb.md
doc/04_architecture/REQ-LIB-ERROR-DEEP-4aeb.md
doc/05_design/REQ-LIB-ERROR-DEEP-4aeb.md

## Scenarios

### error_deep stdlib behavior oracles

#### match destructures Some

- Verify: match destructures Some
   - Expected: x equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ERROR-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-ERROR-DEEP-4aeb
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
# @req: REQ-LIB-ERROR-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-ERROR-DEEP-4aeb
step("Verify: string length and emptiness")
# oracle: 4/0 — len counts chars; only the empty string is empty
expect("test".len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect("".len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect("".is_empty()).to_equal(true)
```

</details>

#### comparison ordering

- Verify: comparison ordering
   - Expected: 1 < 2 is true
   - Expected: 2 <= 2 is true
   - Expected: 3 > 4 is false
   - Expected: 5 == 5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ERROR-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-ERROR-DEEP-4aeb
step("Verify: comparison ordering")
# oracle: transitive i64 ordering as written
expect(1 < 2).to_equal(true)
expect(2 <= 2).to_equal(true)
expect(3 > 4).to_equal(false)
expect(5 == 5).to_equal(true)
```

</details>

#### integer arithmetic and abs

- Verify: integer arithmetic and abs
   - Expected: abs(-5) equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 equals `1024)  # oracle: pinned constant asserted by this scenario`
   - Expected: 7 / 2 equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: 7 % 3 equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ERROR-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-ERROR-DEEP-4aeb
step("Verify: integer arithmetic and abs")
# oracle: 5 — abs(-5) is the absolute value; 1024 — 2^10
expect(abs(-5)).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2).to_equal(1024)  # oracle: pinned constant asserted by this scenario
expect(7 / 2).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(7 % 3).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### float math min max sqrt floor ceil

- Verify: float math min max sqrt floor ceil
   - Expected: min(3.0, 7.0) equals `3.0`
   - Expected: max(3.0, 7.0) equals `7.0`
   - Expected: sqrt(16.0) equals `4.0`
   - Expected: floor(2.7) equals `2.0`
   - Expected: ceil(2.1) equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ERROR-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-ERROR-DEEP-4aeb
step("Verify: float math min max sqrt floor ceil")
# oracle: 3.0/7.0 — min/max pick the smaller/larger operand; 4.0 — sqrt(16)
expect(min(3.0, 7.0)).to_equal(3.0)
expect(max(3.0, 7.0)).to_equal(7.0)
expect(sqrt(16.0)).to_equal(4.0)
expect(floor(2.7)).to_equal(2.0)
expect(ceil(2.1)).to_equal(3.0)
```

</details>

#### text case conversion

- Verify: text case conversion
   - Expected: "hello".upper() equals `HELLO`
   - Expected: "HELLO".lower() equals `hello`
   - Expected: "Hello".upper() equals `HELLO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ERROR-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-ERROR-DEEP-4aeb
step("Verify: text case conversion")
# oracle: "HELLO"/"hello" — upper/lower are exact case maps
expect("hello".upper()).to_equal("HELLO")
expect("HELLO".lower()).to_equal("hello")
expect("Hello".upper()).to_equal("HELLO")
```

</details>

#### text split trim contains prefix

- Verify: text split trim contains prefix
   - Expected: "hello world".split(" ").len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: "  x  ".trim() equals `x`
   - Expected: "hello" contains `ell`
   - Expected: "hello".starts_with("he") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ERROR-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-ERROR-DEEP-4aeb
step("Verify: text split trim contains prefix")
# oracle: 2 — "hello world" splits into 2 fields on a single space
expect("hello world".split(" ").len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect("  x  ".trim()).to_equal("x")
expect("hello".contains("ell")).to_equal(true)
expect("hello".starts_with("he")).to_equal(true)
```

</details>

#### text replace

- Verify: text replace
   - Expected: "hello".replace("l", "L") equals `heLLo`
   - Expected: "aaa".replace("a", "b") equals `bbb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-ERROR-001
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# @req: REQ-LIB-ERROR-DEEP-4aeb
step("Verify: text replace")
# oracle: "heLLo" — every 'l' replaced by 'L'
expect("hello".replace("l", "L")).to_equal("heLLo")
expect("aaa".replace("a", "b")).to_equal("bbb")
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

- Canonical SPipe generation for source `3b09045c3b7dab6a65fcf7a3bfc7a146e61b256a7cbda3999555ba744b13b94a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b09045c3b7dab6a65fcf7a3bfc7a146e61b256a7cbda3999555ba744b13b94a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b09045c3b7dab6a65fcf7a3bfc7a146e61b256a7cbda3999555ba744b13b94a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/std/deep/error_deep_12_spec.spl
mirror: doc/06_spec/01_unit/std/deep/error_deep_12_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/deep/error_deep_12_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/deep/error_deep_12_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/deep/error_deep_12_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/deep/error_deep_12_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
