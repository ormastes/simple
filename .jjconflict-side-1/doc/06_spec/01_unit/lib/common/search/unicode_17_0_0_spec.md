# unicode_17_0_0_spec

> Executable parity checks for the generated, host-independent UCD 17 adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# unicode_17_0_0_spec

Executable parity checks for the generated, host-independent UCD 17 adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/unicode_17_0_0_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Executable parity checks for the generated, host-independent UCD 17 adapter.

## Scenarios

### pinned Unicode 17 generated adapter

#### classifies token scalars without host Unicode tables

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies token scalars without host Unicode tables
- Verify Unicode 17 categories and underscore token policy
   - Expected: unicode_is_alphabetic(0x11DB0) is true
   - Expected: unicode_is_decimal_number(0x0665) is true
   - Expected: unicode_is_mark(0x0301) is true
   - Expected: unicode_is_token_code_point(0x005F) is true
   - Expected: unicode_is_token_code_point(0x002D) is false
   - Expected: unicode_canonical_combining_class(0x0301) equals `230`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies token scalars without host Unicode tables")
step("Verify Unicode 17 categories and underscore token policy")
expect(unicode_is_alphabetic(0x11DB0)).to_equal(true)
expect(unicode_is_decimal_number(0x0665)).to_equal(true)
expect(unicode_is_mark(0x0301)).to_equal(true)
expect(unicode_is_token_code_point(0x005F)).to_equal(true)
expect(unicode_is_token_code_point(0x002D)).to_equal(false)
expect(unicode_canonical_combining_class(0x0301)).to_equal(230)
```

</details>

#### normalizes canonical and algorithmic Hangul compositions

- normalizes canonical and algorithmic Hangul compositions
- Verify NFC canonical composition and Hangul algorithm
   - Expected: unicode_normalize_nfc(text_from_codepoints([0x0041, 0x030A])) equals `text_from_codepoints([0x00C5])`
   - Expected: unicode_normalize_nfc(text_from_codepoints([0x1100, 0x1161, 0x11A8])) equals `text_from_codepoints([0xAC01])`
   - Expected: unicode_normalize_nfc(text_from_codepoints([0x0F73])) equals `text_from_codepoints([0x0F71, 0x0F72])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes canonical and algorithmic Hangul compositions")
step("Verify NFC canonical composition and Hangul algorithm")
expect(unicode_normalize_nfc(text_from_codepoints([0x0041, 0x030A]))).to_equal(text_from_codepoints([0x00C5]))
expect(unicode_normalize_nfc(text_from_codepoints([0x1100, 0x1161, 0x11A8]))).to_equal(text_from_codepoints([0xAC01]))
expect(unicode_normalize_nfc(text_from_codepoints([0x0F73]))).to_equal(text_from_codepoints([0x0F71, 0x0F72]))
```

</details>

#### applies default lowercase including final sigma and expansion

- applies default lowercase including final sigma and expansion
- Verify locale-independent Default Lowercase Conversion
   - Expected: unicode_default_lowercase(text_from_codepoints([0x039F, 0x03A3])) equals `text_from_codepoints([0x03BF, 0x03C2])`
   - Expected: unicode_default_lowercase(text_from_codepoints([0x039F, 0x03A3, 0x0391])) equals `text_from_codepoints([0x03BF, 0x03C3, 0x03B1])`
   - Expected: text_codepoints(unicode_default_lowercase(text_from_codepoints([0x0130]))) equals `[0x0069, 0x0307]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies default lowercase including final sigma and expansion")
step("Verify locale-independent Default Lowercase Conversion")
expect(unicode_default_lowercase(text_from_codepoints([0x039F, 0x03A3]))).to_equal(text_from_codepoints([0x03BF, 0x03C2]))
expect(unicode_default_lowercase(text_from_codepoints([0x039F, 0x03A3, 0x0391]))).to_equal(text_from_codepoints([0x03BF, 0x03C3, 0x03B1]))
expect(text_codepoints(unicode_default_lowercase(text_from_codepoints([0x0130])))).to_equal([0x0069, 0x0307])
```

</details>

#### passes all five NFC relations in the complete UCD normalization corpus

- passes all five NFC relations in the complete UCD normalization corpus
- Verify every NormalizationTest.txt vector through the generated Simple runtime
   - Expected: _unicode_normalization_corpus_receipt() equals `[20034, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes all five NFC relations in the complete UCD normalization corpus")
step("Verify every NormalizationTest.txt vector through the generated Simple runtime")
expect(_unicode_normalization_corpus_receipt()).to_equal([20034, 0])
```

</details>

#### matches the JavaScript every-scalar Unicode 17 fingerprint

- matches the JavaScript every-scalar Unicode 17 fingerprint
- Verify properties, CCC, singleton NFC, and singleton lowercase for every Unicode scalar
   - Expected: _unicode_scalar_parity_fingerprint() equals `[566308199, 235371174]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the JavaScript every-scalar Unicode 17 fingerprint")
step("Verify properties, CCC, singleton NFC, and singleton lowercase for every Unicode scalar")
expect(_unicode_scalar_parity_fingerprint()).to_equal([566308199, 235371174])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SPK-SEARCH-UNICODE-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ca295edcae3898a06e20afbde431ecab81603fe6e86569b33c55a580f13bee0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ca295edcae3898a06e20afbde431ecab81603fe6e86569b33c55a580f13bee0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ca295edcae3898a06e20afbde431ecab81603fe6e86569b33c55a580f13bee0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/search/unicode_17_0_0_spec.spl
mirror: doc/06_spec/01_unit/lib/common/search/unicode_17_0_0_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/search/unicode_17_0_0_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/search/unicode_17_0_0_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/search/unicode_17_0_0_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/search/unicode_17_0_0_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/search/unicode_17_0_0_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies token scalars without host Unicode tables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/unicode_17_0_0_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes canonical and algorithmic Hangul compositions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/unicode_17_0_0_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies default lowercase including final sigma and expansion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
