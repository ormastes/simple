# Pinned HTML tokenizer vector specification

> This specification compares the canonical tokenizer output with every field

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pinned HTML tokenizer vector specification

This specification compares the canonical tokenizer output with every field

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/html5lib_tokenizer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This specification compares the canonical tokenizer output with every field
represented by the pinned fixture schema. Adjacent character tokens are
coalesced because token chunk boundaries are not observable HTML semantics.

The fixtures are a curated local subset, not a claim that the upstream
html5lib tokenizer suite passes. Corpus placeholders remain explicitly
inadmissible as conformance evidence.

## Scenarios

### Pinned HTML tokenizer vectors

#### should exactly match every normalized token in test1

- should exactly match every normalized token in test1
- Load the first pinned tokenizer vector set
   - Expected: _fixture_failure_count("test1.json") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("should exactly match every normalized token in test1")
step("Load the first pinned tokenizer vector set")
val fixture = _load_fixture("test1.json")
expect(fixture.len()).to_be_greater_than(0)
expect(_fixture_failure_count("test1.json")).to_equal(0)
```

</details>

#### should exactly match every normalized token in test2

- should exactly match every normalized token in test2
- Load the second pinned tokenizer vector set
   - Expected: _fixture_failure_count("test2.json") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("should exactly match every normalized token in test2")
step("Load the second pinned tokenizer vector set")
val fixture = _load_fixture("test2.json")
expect(fixture.len()).to_be_greater_than(0)
expect(_fixture_failure_count("test2.json")).to_equal(0)
```

</details>

#### should reject a known expected-token mutation

- should reject a known expected-token mutation
- Change the expected start-tag name while keeping the input fixed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("should reject a known expected-token mutation")
step("Change the expected start-tag name while keeping the input fixed")
val mutated = json_parse(
    "[[\"StartTag\",\"wrong\",{}]," +
    "[\"Character\",\"hello\"],[\"EndTag\",\"p\"],[\"EOF\"]]"
)
expect(_case_matches_expected(
    "<p>hello</p>", mutated
)).to_equal(false)
```

</details>

#### should reject changed fixture provenance and missing descriptions

- should reject changed fixture provenance and missing descriptions
- Change the declared normalization and token field schema
- Require a nonempty description on every loaded case


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("should reject changed fixture provenance and missing descriptions")
step("Change the declared normalization and token field schema")
val changed_provenance = json_parse(
    "{\"schema\":\"simple-html-token-v1\",\"provenance\":{" +
    "\"kind\":\"curated-local\"," +
    "\"upstream_html5lib_import\":\"not-imported\"," +
    "\"normalization\":\"different\"," +
    "\"token_fields\":\"kind,data\"}}"
)
val rejects_changed_normalization = not _fixture_contract_valid(
    changed_provenance
)
val changed_fields = json_parse(
    "{\"schema\":\"simple-html-token-v1\",\"provenance\":{" +
    "\"kind\":\"curated-local\"," +
    "\"upstream_html5lib_import\":\"not-imported\"," +
    "\"normalization\":\"coalesce-adjacent-character-tokens\"," +
    "\"token_fields\":\"kind,data\"}}"
)
val rejects_changed_fields = not _fixture_contract_valid(
    changed_fields
)

step("Require a nonempty description on every loaded case")
val undescribed = json_parse(
    "{\"description\":\"\",\"input\":\"x\"," +
    "\"output\":[[\"Character\",\"x\"],[\"EOF\"]]}"
)
val rejects_missing_description = not _fixture_case_metadata_valid(
    undescribed
)
expect(
    "{rejects_changed_normalization}|" +
    "{rejects_changed_fields}|{rejects_missing_description}"
).to_equal("true|true|true")
```

</details>

### Retained HTML corpus admission

<details>
<summary>Advanced: should reject empty and placeholder baselines as conformance evidence</summary>

#### should reject empty and placeholder baselines as conformance evidence

- should reject empty and placeholder baselines as conformance evidence
- Inspect the retained site corpus baseline
   - Expected: _corpus_baseline_is_admissible("") is false
   - Expected: _corpus_baseline_is_admissible(content) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("should reject empty and placeholder baselines as conformance evidence")
step("Inspect the retained site corpus baseline")
val content = read_file_text(
    "test/09_baselines/famous_site_corpus/site_0/baseline.txt"
)
expect(_corpus_baseline_is_admissible("")).to_equal(false)
expect(_corpus_baseline_is_admissible(content)).to_equal(false)
```

</details>


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

- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cd7599e06b4596171274d0cfda2c29baedb66dbd5533b6bec1cd680f9004c907`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd7599e06b4596171274d0cfda2c29baedb66dbd5533b6bec1cd680f9004c907`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd7599e06b4596171274d0cfda2c29baedb66dbd5533b6bec1cd680f9004c907`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/01_unit/browser_engine/html5lib_tokenizer_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/html5lib_tokenizer_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/html5lib_tokenizer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/html5lib_tokenizer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:214:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exactly match every normalized token in test1' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:214:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exactly match every normalized token in test1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:224:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exactly match every normalized token in test2' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:224:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exactly match every normalized token in test2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:234:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a known expected-token mutation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:234:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a known expected-token mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:248:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject changed fixture provenance and missing descriptions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/browser_engine/html5lib_tokenizer_spec.spl:289:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject empty and placeholder baselines as conformance evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
