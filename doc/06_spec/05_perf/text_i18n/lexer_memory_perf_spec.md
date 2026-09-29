# lexer_memory_perf_spec

> Measures the production `CoreLexer`, including its current `source.chars()`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lexer_memory_perf_spec

Measures the production `CoreLexer`, including its current `source.chars()`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/text_i18n/lexer_memory_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Simple lexer memory performance

Measures the production `CoreLexer`, including its current `source.chars()`
materialization. Corpora are constructed before snapshots. Each scan is capped
and must reach the real EOF token, preventing a dead lexer from masquerading as
performance evidence.

## Scenarios

### Simple lexer memory performance

#### records ASCII source materialization and scan growth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_memory_scan("ascii", ascii_source(), 4096)
```

</details>

#### records multilingual string materialization and scan growth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_memory_scan("multilingual", multilingual_source(), 4096)
```

</details>

#### records named i18n interpolation materialization and scan growth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_memory_scan("i18n", i18n_source(), 4096)
```

</details>

#### records broad syntax and indentation scan growth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_memory_scan("syntax-stress", syntax_stress_source(), 4096)
```

</details>

<details>
<summary>Advanced: keeps the lexical edge-probe matrix finite and EOF-complete</summary>

#### keeps the lexical edge-probe matrix finite and EOF-complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probes = lexer_edge_probes()
var token_total: i64 = 0
var checksum: i64 = 0
for source in probes:
    val receipt = lex_receipt(source, 512)
    expect(receipt.reached_eof).to_equal(true)
    token_total = token_total + receipt.tokens
    checksum = checksum + receipt.checksum
expect(probes.len()).to_be_greater_than(20)
expect(token_total).to_be_greater_than(probes.len())
expect(checksum).to_be_greater_than(0)
print "text_memory operation=lexer_edge_matrix probes={probes.len()} tokens={token_total} checksum={checksum} allocation_count=unavailable process_hwm_kib=unavailable"
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d5262b75e223723e6adca0cdc2b48547d09bf372242849621d915fc7d1c7dc9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d5262b75e223723e6adca0cdc2b48547d09bf372242849621d915fc7d1c7dc9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d5262b75e223723e6adca0cdc2b48547d09bf372242849621d915fc7d1c7dc9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/05_perf/text_i18n/lexer_memory_perf_spec.spl
mirror: doc/06_spec/05_perf/text_i18n/lexer_memory_perf_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/text_i18n/lexer_memory_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/text_i18n/lexer_memory_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/text_i18n/lexer_memory_perf_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/05_perf/text_i18n/lexer_memory_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/05_perf/text_i18n/lexer_memory_perf_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/05_perf/text_i18n/lexer_memory_perf_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/05_perf/text_i18n/lexer_memory_perf_spec.spl:136:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records ASCII source materialization and scan growth' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/05_perf/text_i18n/lexer_memory_perf_spec.spl:139:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records multilingual string materialization and scan growth' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/05_perf/text_i18n/lexer_memory_perf_spec.spl:142:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records named i18n interpolation materialization and scan growth' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/05_perf/text_i18n/lexer_memory_perf_spec.spl:145:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records broad syntax and indentation scan growth' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
