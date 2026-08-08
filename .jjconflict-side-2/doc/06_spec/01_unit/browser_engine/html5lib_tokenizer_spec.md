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
| Updated | 2026-07-29 |
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

- Load the first pinned tokenizer vector set
   - Expected: _fixture_failure_count("test1.json") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the first pinned tokenizer vector set")
val fixture = _load_fixture("test1.json")
expect(fixture.len()).to_be_greater_than(0)
expect(_fixture_failure_count("test1.json")).to_equal(0)
```

</details>

#### should exactly match every normalized token in test2

- Load the second pinned tokenizer vector set
   - Expected: _fixture_failure_count("test2.json") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the second pinned tokenizer vector set")
val fixture = _load_fixture("test2.json")
expect(fixture.len()).to_be_greater_than(0)
expect(_fixture_failure_count("test2.json")).to_equal(0)
```

</details>

#### should reject a known expected-token mutation

- Change the expected start-tag name while keeping the input fixed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Change the declared normalization and token field schema
- Require a nonempty description on every loaded case


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect the retained site corpus baseline
   - Expected: _corpus_baseline_is_admissible("") is false
   - Expected: _corpus_baseline_is_admissible(content) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
