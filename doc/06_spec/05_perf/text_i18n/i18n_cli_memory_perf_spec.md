# i18n_cli_memory_perf_spec

> Legacy i18n CLI extraction and catalog memory-performance smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# i18n_cli_memory_perf_spec

Legacy i18n CLI extraction and catalog memory-performance smoke.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/text_i18n/i18n_cli_memory_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Legacy i18n CLI extraction and catalog memory-performance smoke.

## Scenarios

### i18n CLI extraction memory performance

#### extracts multilingual catalogs with bounded output and explicit memory availability

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val corpus = cli_perf_corpus(256)
var samples: [i64] = []
var catalog_bytes: i64 = 0
var template_bytes: i64 = 0
var checksum: i64 = 0
var sample: i64 = 0
while sample < 7:
    val started = time_now_unix_micros()
    val strings = extract_i18n_strings(corpus, "perf.spl")
    val catalog = generate_locale_catalog(strings)
    val template = generate_locale_template("ko-KR", strings)
    samples.push(time_now_unix_micros() - started)
    expect(strings.len()).to_equal(256)
    catalog_bytes = catalog.len()
    template_bytes = template.len()
    checksum = checksum + strings.len() + catalog_bytes + template_bytes
    sample = sample + 1
val latency = cli_perf_percentiles(samples)
val hwm = cli_perf_hwm_kib()
expect(latency[1]).to_be_less_than(5000001)
expect(hwm).to_be_greater_than(0)
print "text_perf operation=i18n_cli_extract_catalog samples=7 messages=256" +
    " input_bytes={corpus.len()} catalog_bytes={catalog_bytes}" +
    " template_bytes={template_bytes} p50_us={latency[0]}" +
    " p95_us={latency[1]} process_hwm_kib={hwm}" +
    " allocation_count=unavailable allocated_bytes=unavailable" +
    " transient_bytes=unavailable retained_bytes=unavailable checksum={checksum}"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4bdf9c518791515f2a78dad45d29628ee443b67c802cb444c435bd032d8409f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4bdf9c518791515f2a78dad45d29628ee443b67c802cb444c435bd032d8409f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4bdf9c518791515f2a78dad45d29628ee443b67c802cb444c435bd032d8409f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/05_perf/text_i18n/i18n_cli_memory_perf_spec.spl
mirror: doc/06_spec/05_perf/text_i18n/i18n_cli_memory_perf_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=90 oracle=90
  traceability=80 evidence=100 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/text_i18n/i18n_cli_memory_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/text_i18n/i18n_cli_memory_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/text_i18n/i18n_cli_memory_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/05_perf/text_i18n/i18n_cli_memory_perf_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/05_perf/text_i18n/i18n_cli_memory_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/text_i18n/i18n_cli_memory_perf_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/05_perf/text_i18n/i18n_cli_memory_perf_spec.spl:41:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'extracts multilingual catalogs with bounded output and explicit memory availability' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
