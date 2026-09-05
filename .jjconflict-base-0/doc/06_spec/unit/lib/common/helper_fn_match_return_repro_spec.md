# Helper Fn Match Return Repro Specification

> Tests covering helper-fn match return regression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helper Fn Match Return Repro Specification

## Scenarios

### helper-fn match return regression

#### D1: int from match in helper called from it-block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- D1: int from match in helper called from it-block
   - Expected: _h_int(0) equals `100`
   - Expected: _h_int(5) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("D1: int from match in helper called from it-block")
expect(_h_int(0)).to_equal(100)
expect(_h_int(5)).to_equal(200)
```

</details>

#### D2: text from match in helper called from it-block

- D2: text from match in helper called from it-block
   - Expected: _h_text(0) equals `zero`
   - Expected: _h_text(5) equals `nonzero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("D2: text from match in helper called from it-block")
expect(_h_text(0)).to_equal("zero")
expect(_h_text(5)).to_equal("nonzero")
```

</details>

#### D4: bool from match in helper called from it-block

- D4: bool from match in helper called from it-block
   - Expected: _h_bool(0) is true
   - Expected: _h_bool(5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("D4: bool from match in helper called from it-block")
expect(_h_bool(0)).to_equal(true)
expect(_h_bool(5)).to_equal(false)
```

</details>

#### D6: single-arm match returning bool

- D6: single-arm match returning bool
   - Expected: _h_bool_single(0) is true
   - Expected: _h_bool_single(99) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("D6: single-arm match returning bool")
expect(_h_bool_single(0)).to_equal(true)
expect(_h_bool_single(99)).to_equal(true)
```

</details>

#### D8: bool via same-module Result<bool, text> match (mirrors _hs256_verify_ok)

- D8: bool via same-module Result<bool, text> match (mirrors _hs256_verify_ok)
   - Expected: _h_bool_via_result(0) is true
   - Expected: _h_bool_via_result(5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("D8: bool via same-module Result<bool, text> match (mirrors _hs256_verify_ok)")
expect(_h_bool_via_result(0)).to_equal(true)
expect(_h_bool_via_result(5)).to_equal(false)
```

</details>

#### D9: bool via cross-module Result<bool, text> match (exact _hs256_verify_ok shape)

- D9: bool via cross-module Result<bool, text> match (exact _hs256_verify_ok shape)
   - Expected: _h_bool_via_jwt(compact, key) is true
   - Expected: _h_bool_via_jwt(compact, wrong_key) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("D9: bool via cross-module Result<bool, text> match (exact _hs256_verify_ok shape)")
var key: [u8] = []
var i = 0
while i < 32:
    key.push(((i * 7 + 13) % 256).to_u8())
    i = i + 1
var wrong_key: [u8] = []
var j = 0
while j < 32:
    wrong_key.push(((j * 3 + 99) % 256).to_u8())
    j = j + 1
val payload = "{\"sub\":\"regress\"}"
val compact = jwt_sign_hs256(payload, key)
expect(_h_bool_via_jwt(compact, key)).to_equal(true)
expect(_h_bool_via_jwt(compact, wrong_key)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/helper_fn_match_return_repro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering helper-fn match return regression.
- helper-fn match return regression

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `240c9448b44e8086a67eee0091462db9a774f6e395deb1dcdddecac0e767aceb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `240c9448b44e8086a67eee0091462db9a774f6e395deb1dcdddecac0e767aceb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `240c9448b44e8086a67eee0091462db9a774f6e395deb1dcdddecac0e767aceb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/helper_fn_match_return_repro_spec.spl
mirror: doc/06_spec/unit/lib/common/helper_fn_match_return_repro_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/helper_fn_match_return_repro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/helper_fn_match_return_repro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/helper_fn_match_return_repro_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/helper_fn_match_return_repro_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'D1: int from match in helper called from it-block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/helper_fn_match_return_repro_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'D2: text from match in helper called from it-block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/helper_fn_match_return_repro_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'D4: bool from match in helper called from it-block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
