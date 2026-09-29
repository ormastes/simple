# duplicate_check_spec

> Purpose: Prove that duplicate-check config.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# duplicate_check_spec

Purpose: Prove that duplicate-check config.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/duplicate_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that duplicate-check config.
Audience: APP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### duplicate-check config

#### loads semantic-first defaults while keeping token mode available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads semantic-first defaults while keeping token mode available
- Verify: loads semantic-first defaults while keeping token mode available
   - Expected: config.use_semantic is true
   - Expected: config.use_cosine_similarity is false
   - Expected: config.min_tokens equals `30`
   - Expected: config.min_lines equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads semantic-first defaults while keeping token mode available")
step("Verify: loads semantic-first defaults while keeping token mode available")
# @req: REQ-APP-DUPLICATE-CHECK-CONFIG-001
val config = default_config()
expect(config.use_semantic).to_equal(true)
expect(config.use_cosine_similarity).to_equal(false)
expect(config.min_tokens).to_equal(30)
expect(config.min_lines).to_equal(5)
```

</details>

### duplicate-check tokenizer

#### tokenizes simple code

- tokenizes simple code
- Verify: tokenizes simple code
   - Expected: tokens[0].value equals `fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes simple code")
step("Verify: tokenizes simple code")
var config = default_config()
config.use_semantic = false
config.ignore_identifiers = false
val source = "fn test(value: i64) -> i64:\n    value + 1\n"
val tokens = tokenize(source, config)
expect(tokens.len()).to_be_greater_than(0)
expect(tokens[0].value).to_equal("fn")
```

</details>

#### normalizes identifiers when configured

- normalizes identifiers when configured
- Verify: normalizes identifiers when configured
   - Expected: has_identifier_token is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes identifiers when configured")
step("Verify: normalizes identifiers when configured")
var config = default_config()
config.use_semantic = false
config.ignore_identifiers = true
val source = "var count = total + 1"
val tokens = tokenize(source, config)
var has_identifier_token = false
for token in tokens:
    if token.kind == SimpleTokenKind.Identifier and token.value == "IDENTIFIER":
        has_identifier_token = true
expect(has_identifier_token).to_equal(true)
```

</details>

### duplicate-check file collection

#### collects fixture files from directory

- collects fixture files from directory
- Verify: collects fixture files from directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects fixture files from directory")
step("Verify: collects fixture files from directory")
expect(fixture_root()).to_start_with(cwd() + "/test/fixtures/")
var config = default_config()
config.use_semantic = false
config.exclude_patterns = []
val files = collect_files(fixture_root(), config)
expect(files.len()).to_be_greater_than(3)
```

</details>

#### excludes files by pattern

- excludes files by pattern
- Verify: excludes files by pattern
   - Expected: has_doc_fixture is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes files by pattern")
step("Verify: excludes files by pattern")
var config = default_config()
config.use_semantic = false
config.exclude_patterns = ["doc_fixture"]
val files = collect_files(fixture_root(), config)
var has_doc_fixture = false
for file in files:
    if file.contains("doc_fixture"):
        has_doc_fixture = true
expect(has_doc_fixture).to_equal(false)
```

</details>

### duplicate-check features

#### extracts token frequencies

- extracts token frequencies
- Verify: extracts token frequencies
   - Expected: freq_map["SimpleTokenKind::Keyword:fn"] equals `1`
   - Expected: freq_map["SimpleTokenKind::Identifier:test"] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts token frequencies")
step("Verify: extracts token frequencies")
val tokens = [
    SimpleToken(kind: SimpleTokenKind.Keyword, value: "fn", line: 1, column: 1, start_offset: 0, end_offset: 2),
    SimpleToken(kind: SimpleTokenKind.Identifier, value: "test", line: 1, column: 4, start_offset: 3, end_offset: 7),
    SimpleToken(kind: SimpleTokenKind.Identifier, value: "test", line: 1, column: 9, start_offset: 8, end_offset: 12)
]

val freq_map = extract_token_frequencies(tokens, 0, 3)
expect(freq_map["SimpleTokenKind::Keyword:fn"]).to_equal(1)
expect(freq_map["SimpleTokenKind::Identifier:test"]).to_equal(2)
```

</details>

#### computes cosine similarity for identical vectors

- computes cosine similarity for identical vectors
- Verify: computes cosine similarity for identical vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes cosine similarity for identical vectors")
step("Verify: computes cosine similarity for identical vectors")
var freq_map = {}
freq_map["SimpleTokenKind::Keyword:fn"] = 1
freq_map["SimpleTokenKind::Identifier:test"] = 2

val vector1 = build_feature_vector(0, freq_map)
val vector2 = build_feature_vector(1, freq_map)
val similarity = cosine_similarity(vector1, vector2)

expect(similarity).to_be_greater_than(0.99)
```

</details>

#### computes cosine similarity for different vectors

- computes cosine similarity for different vectors
- Verify: computes cosine similarity for different vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes cosine similarity for different vectors")
step("Verify: computes cosine similarity for different vectors")
var freq_map1 = {}
freq_map1["SimpleTokenKind::Keyword:fn"] = 1
freq_map1["SimpleTokenKind::Identifier:test"] = 2

var freq_map2 = {}
freq_map2["SimpleTokenKind::Keyword:var"] = 1
freq_map2["SimpleTokenKind::Identifier:count"] = 1

val vector1 = build_feature_vector(0, freq_map1)
val vector2 = build_feature_vector(1, freq_map2)
val similarity = cosine_similarity(vector1, vector2)

expect(similarity).to_be_less_than(1.0)
```

</details>

### duplicate-check semantic fallback

#### detects similar docs without ollama

- detects similar docs without ollama
- Verify: detects similar docs without ollama
   - Expected: report.matches.len() equals `1`
   - Expected: report.matches[0].match_kind contains `text-based`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects similar docs without ollama")
step("Verify: detects similar docs without ollama")
val entries = [
    DocEntry(
        file_path: "a.spl",
        line_number: 1,
        item_name: "sum_values",
        item_kind: "fn",
        signature: "fn sum_values(values: [i64]) -> i64",
        doc_comment: "Compute the total sum of all values in the input list and return the accumulated result.",
        has_doc: true
    ),
    DocEntry(
        file_path: "b.spl",
        line_number: 1,
        item_name: "sum_numbers",
        item_kind: "fn",
        signature: "fn sum_numbers(numbers: [i64]) -> i64",
        doc_comment: "Compute the total sum of all values in the input list and return the accumulated result.",
        has_doc: true
    )
]
val report = run_text_fallback(entries, 0.90, 0.40)
expect(report.matches.len()).to_equal(1)
expect(report.matches[0].match_kind.contains("text-based")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-DUPLICATE-CHECK-CONFIG-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `13b3e11a11f5f8f154873b2f4058763212b7c0ad9e6b08a9c837530c4e20c263`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13b3e11a11f5f8f154873b2f4058763212b7c0ad9e6b08a9c837530c4e20c263`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13b3e11a11f5f8f154873b2f4058763212b7c0ad9e6b08a9c837530c4e20c263`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/duplicate_check_spec.spl
mirror: doc/06_spec/unit/app/duplicate_check_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/duplicate_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/duplicate_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/duplicate_check_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/duplicate_check_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads semantic-first defaults while keeping token mode available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/duplicate_check_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes simple code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/duplicate_check_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes identifiers when configured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
