# Analyzer Contract Specification

> Tests covering search analyzer contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Analyzer Contract Specification

## Scenarios

### search analyzer contract

#### keeps positions across removed stop words and marks exact identifiers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps positions across removed stop words and marks exact identifiers
- Check positioned Unicode tokens
   - Expected: terms.len() equals `2`
   - Expected: terms[0].value equals `alpha`
   - Expected: terms[0].position equals `1`
   - Expected: terms[1].position equals `3`
   - Expected: ids[ids.len() - 1].exact_identifier is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps positions across removed stop words and marks exact identifiers")
step("Check positioned Unicode tokens")
val terms = analyze_positioned("Alpha and BETA", false)
expect(terms.len()).to_equal(2)
expect(terms[0].value).to_equal("alpha")
expect(terms[0].position).to_equal(1)
expect(terms[1].position).to_equal(3)
val ids = analyze_positioned("REQ-SEARCH-001", true)
expect(ids[ids.len() - 1].exact_identifier).to_equal(true)
```

</details>

#### does not claim frozen SPipe parity before UCD fixtures exist

- does not claim frozen SPipe parity before UCD fixtures exist
- Check honest analyzer identity
   - Expected: AnalyzerIdentity.simple_preview_v1().claims_spipe_unicode_parity() is false
   - Expected: AnalyzerIdentity.spipe_v1().claims_spipe_unicode_parity() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not claim frozen SPipe parity before UCD fixtures exist")
step("Check honest analyzer identity")
expect(AnalyzerIdentity.simple_preview_v1().claims_spipe_unicode_parity()).to_equal(false)
expect(AnalyzerIdentity.spipe_v1().claims_spipe_unicode_parity()).to_equal(true)
expect(AnalyzerIdentity.spipe_v1().unicode_table_binding()).to_start_with("17.0.0:sha256:")
```

</details>

#### normalizes lowercase tokens without collapsing stop-word positions

- normalizes lowercase tokens without collapsing stop-word positions
- Check normalization and exact position vectors
   - Expected: terms[0].value equals `äpfel`
   - Expected: terms[0].position equals `1`
   - Expected: terms[1].position equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes lowercase tokens without collapsing stop-word positions")
step("Check normalization and exact position vectors")
val terms = analyze_positioned("ÄPFEL the Σ", false)
expect(terms[0].value).to_equal("äpfel")
expect(terms[0].position).to_equal(1)
expect(terms[1].position).to_equal(3)
```

</details>

#### matches generated Unicode 17 NFC lowercase and category vectors

- matches generated Unicode 17 NFC lowercase and category vectors
- Verify executable generated table parity
   - Expected: unicode_normalize_nfc("e\u{0301}") equals `é`
   - Expected: unicode_default_lowercase("ΟΣ") equals `ος`
   - Expected: unicode_default_lowercase("ΟΣΑ") equals `οσα`
   - Expected: unicode_is_alphabetic(0x03A3) is true
   - Expected: unicode_is_decimal_number(0x0661) is true
   - Expected: unicode_is_mark(0x0301) is true
   - Expected: unicode_is_token_code_point(95) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches generated Unicode 17 NFC lowercase and category vectors")
step("Verify executable generated table parity")
expect(unicode_normalize_nfc("e\u{0301}")).to_equal("é")
expect(unicode_default_lowercase("ΟΣ")).to_equal("ος")
expect(unicode_default_lowercase("ΟΣΑ")).to_equal("οσα")
expect(unicode_is_alphabetic(0x03A3)).to_equal(true)
expect(unicode_is_decimal_number(0x0661)).to_equal(true)
expect(unicode_is_mark(0x0301)).to_equal(true)
expect(unicode_is_token_code_point(95)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/analyzer_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering search analyzer contract.
- search analyzer contract

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `345f3ba833aa51112585ee5ae5f3e44b022f7e4a00d3cd5b4cc6b31cd80afcdc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `345f3ba833aa51112585ee5ae5f3e44b022f7e4a00d3cd5b4cc6b31cd80afcdc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `345f3ba833aa51112585ee5ae5f3e44b022f7e4a00d3cd5b4cc6b31cd80afcdc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/search/analyzer_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/search/analyzer_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/search/analyzer_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/search/analyzer_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/search/analyzer_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/search/analyzer_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps positions across removed stop words and marks exact identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/analyzer_contract_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not claim frozen SPipe parity before UCD fixtures exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/analyzer_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes lowercase tokens without collapsing stop-word positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
