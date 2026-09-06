# knowledge_contract_spec

> Wave 4 canonical common-search records and deterministic behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# knowledge_contract_spec

Wave 4 canonical common-search records and deterministic behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/knowledge_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Wave 4 canonical common-search records and deterministic behavior.

## Scenarios

### canonical lexical search contract

#### preserves exact normalized identifiers while tokenizing prose

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves exact normalized identifiers while tokenizing prose
- Analyze prose and identifiers deterministically
   - Expected: analyze_text("Alpha, BETA!") equals `["alpha", "beta"]`
   - Expected: analyze_text("ÄPFEL") equals `["äpfel"]`
   - Expected: analyze_identifier("REQ-SEARCH_001") equals `["req-search_001", "req", "search", "001"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves exact normalized identifiers while tokenizing prose")
step("Analyze prose and identifiers deterministically")
expect(analyze_text("Alpha, BETA!")).to_equal(["alpha", "beta"])
expect(analyze_text("ÄPFEL")).to_equal(["äpfel"])
expect(analyze_identifier("REQ-SEARCH_001")).to_equal(["req-search_001", "req", "search", "001"])
expect(AnalyzerIdentity.spipe_v1().cache_key()).to_contain("ucd-17.0.0")
```

</details>

#### tracks exact corpus length and term document frequency

- tracks exact corpus length and term document frequency
- Build exact corpus statistics
   - Expected: stats.document_count equals `2`
   - Expected: stats.average_document_length_fixed equals `2500000`
   - Expected: stats.document_frequency("alpha") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tracks exact corpus length and term document frequency")
step("Build exact corpus statistics")
val stats = CorpusStats.of([2, 3], [TermCorpusStat.of("alpha", 2)])
expect(stats.document_count).to_equal(2)
expect(stats.average_document_length_fixed).to_equal(2500000)
expect(stats.document_frequency("alpha")).to_equal(2)
```

</details>

#### rejects malformed BM25 inputs and preserves the absolute oracle

- rejects malformed BM25 inputs and preserves the absolute oracle
- Use checked fixed-point BM25
   - Expected: invalid.is_ok() is false
   - Expected: valid.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed BM25 inputs and preserves the absolute oracle")
step("Use checked fixed-point BM25")
val invalid = bm25_score_default_checked([1], [1, 2], 2, 2000000, 2)
expect(invalid.is_ok()).to_equal(false)
val valid = bm25_score_default_checked([1], [1], 2, 2000000, 2)
expect(valid.is_ok()).to_equal(true)
expect(valid.unwrap().raw_value()).to_be_greater_than(0)
```

</details>

#### breaks score ties by ascending public text ID

- breaks score ties by ascending public text ID
- Rank text IDs with deterministic tie-breaking
   - Expected: ranked[0].document_id equals `middle`
   - Expected: ranked[1].document_id equals `alpha`
   - Expected: ranked[2].document_id equals `zeta`
   - Expected: ranked[0].rank equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("breaks score ties by ascending public text ID")
step("Rank text IDs with deterministic tie-breaking")
val ranked = text_top_k([
    TextScoredDoc.of("zeta", Score.from_milli(700)),
    TextScoredDoc.of("alpha", Score.from_milli(700)),
    TextScoredDoc.of("middle", Score.from_milli(900)),
], 3)
expect(ranked[0].document_id).to_equal("middle")
expect(ranked[1].document_id).to_equal("alpha")
expect(ranked[2].document_id).to_equal("zeta")
expect(ranked[0].rank).to_equal(1)
```

</details>

#### applies snapshot deltas only to the declared base

- applies snapshot deltas only to the declared base
- Apply an immutable base-plus-delta snapshot
   - Expected: applied.is_ok() is true
   - Expected: applied.unwrap().documents.len() equals `2`
   - Expected: applied.unwrap().documents[0].id equals `b`
   - Expected: applied.unwrap().documents[1].id equals `c`
   - Expected: base.apply(stale, "snap-x", "rev-x").is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies snapshot deltas only to the declared base")
step("Apply an immutable base-plus-delta snapshot")
val base = SearchSnapshot.of("snap-1", "rev-1", AnalyzerIdentity.spipe_v1(), [document("a"), document("b")])
val changed = SearchIndexDelta.of("snap-1", [document("c")], ["a"])
val applied = base.apply(changed, "snap-2", "rev-2")
expect(applied.is_ok()).to_equal(true)
expect(applied.unwrap().documents.len()).to_equal(2)
expect(applied.unwrap().documents[0].id).to_equal("b")
expect(applied.unwrap().documents[1].id).to_equal("c")
val stale = SearchIndexDelta.of("wrong", [], [])
expect(base.apply(stale, "snap-x", "rev-x").is_ok()).to_equal(false)
```

</details>

#### bounds query result counts

- bounds query result counts
- Clamp query limits to the provider maximum
   - Expected: query.bounded_limit(1000) equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds query result counts")
step("Clamp query limits to the provider maximum")
val query = SearchQuery.of("alpha", [], 5000, "", false)
expect(query.bounded_limit(1000)).to_equal(1000)
```

</details>

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
- `REQ-SPK-SEARCH-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `542e4ce18235f4a1b69ebf004803e36dc102395c8c086e58afc53fcd44695f62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `542e4ce18235f4a1b69ebf004803e36dc102395c8c086e58afc53fcd44695f62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `542e4ce18235f4a1b69ebf004803e36dc102395c8c086e58afc53fcd44695f62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/search/knowledge_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/search/knowledge_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/search/knowledge_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/search/knowledge_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/search/knowledge_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/search/knowledge_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/search/knowledge_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves exact normalized identifiers while tokenizing prose' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/knowledge_contract_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks exact corpus length and term document frequency' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/knowledge_contract_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed BM25 inputs and preserves the absolute oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
