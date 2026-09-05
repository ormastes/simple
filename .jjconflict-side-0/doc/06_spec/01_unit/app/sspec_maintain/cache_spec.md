# Cache Specification

> Tests covering SSpec per-pair cache identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cache Specification

## Scenarios

### SSpec per-pair cache identity

#### reuses an unchanged source and manual pair

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reuses an unchanged source and manual pair
   - Expected: second.identity equals `first.identity`
   - Expected: sspec_pair_cache_reusable(record, second) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses an unchanged source and manual pair")
val first = pair_key("./test/a_spec.spl", Some("source"),
    "./doc/06_spec/a_spec.md", Some("manual"))
val second = pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/a_spec.md", Some("manual"))
expect(second.identity).to_equal(first.identity)
val record = SspecCacheRecord(schema_version: "sspec-maintain-cache/v1",
    identity: first.identity, effective_score: 80,
    maximum_severity_rank: 2, human_report: "human",
    json_report: "{}", sarif_report: "")
expect(sspec_pair_cache_reusable(record, second)).to_equal(true)
```

</details>

#### invalidates create edit delete move and rename independently

- invalidates create edit delete move and rename independently
   - Expected: created.identity == absent.identity is false
   - Expected: edited.identity == created.identity is false
   - Expected: moved.identity == created.identity is false
   - Expected: renamed.identity == created.identity is false
   - Expected: deleted.identity == created.identity is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates create edit delete move and rename independently")
val absent = pair_key("test/a_spec.spl", None,
    "doc/06_spec/a_spec.md", None)
val created = pair_key("test/a_spec.spl", Some("source-a"),
    "doc/06_spec/a_spec.md", None)
val edited = pair_key("test/a_spec.spl", Some("source-b"),
    "doc/06_spec/a_spec.md", None)
val moved = pair_key("test/sub/a_spec.spl", Some("source-a"),
    "doc/06_spec/sub/a_spec.md", None)
val renamed = pair_key("test/b_spec.spl", Some("source-a"),
    "doc/06_spec/b_spec.md", None)
val deleted = pair_key("test/a_spec.spl", None,
    "doc/06_spec/a_spec.md", None)
expect(created.identity == absent.identity).to_equal(false)
expect(edited.identity == created.identity).to_equal(false)
expect(moved.identity == created.identity).to_equal(false)
expect(renamed.identity == created.identity).to_equal(false)
expect(deleted.identity == created.identity).to_equal(false)
```

</details>

#### invalidates manual path content rule configuration and tool changes

- invalidates manual path content rule configuration and tool changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates manual path content rule configuration and tool changes")
val base = pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/a_spec.md", Some("manual"))
expect(pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/a_spec.md", None).identity == base.identity).to_equal(false)
expect(pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/a_spec.md", Some("changed")).identity == base.identity).to_equal(false)
expect(pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/renamed.md", Some("manual")).identity == base.identity).to_equal(false)
expect(pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/a_spec.md", Some("manual"), rules: "rules/2").identity == base.identity).to_equal(false)
expect(pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/a_spec.md", Some("manual"), config: "config/2").identity == base.identity).to_equal(false)
expect(pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/a_spec.md", Some("manual"), tool: "tool/2").identity == base.identity).to_equal(false)
```

</details>

#### canonicalizes rule filter order but tracks baseline and suppression edits

- canonicalizes rule filter order but tracks baseline and suppression edits
   - Expected: reordered equals `first`
   - Expected: baseline_changed == first is false
   - Expected: suppression_changed == first is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("canonicalizes rule filter order but tracks baseline and suppression edits")
val first = sspec_cache_configuration_identity("baseline", "suppressions",
    ["SSDOC-B", "SSDOC-A", "SSDOC-A"])
val reordered = sspec_cache_configuration_identity("baseline", "suppressions",
    ["SSDOC-A", "SSDOC-B"])
val baseline_changed = sspec_cache_configuration_identity("changed",
    "suppressions", ["SSDOC-A", "SSDOC-B"])
val suppression_changed = sspec_cache_configuration_identity("baseline",
    "changed", ["SSDOC-A", "SSDOC-B"])
expect(reordered).to_equal(first)
expect(baseline_changed == first).to_equal(false)
expect(suppression_changed == first).to_equal(false)
```

</details>

#### uses one stable content-addressed cache path per pair identity

- uses one stable content-addressed cache path per pair identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses one stable content-addressed cache path per pair identity")
val key = pair_key("test/a_spec.spl", Some("source"),
    "doc/06_spec/a_spec.md", None)
expect(sspec_pair_cache_path("cache", key)).to_equal(
    "cache/" + key.identity + ".cache")
```

</details>

#### reassembles cached JSON and SARIF fragments without changing format

- reassembles cached JSON and SARIF fragments without changing format


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassembles cached JSON and SARIF fragments without changing format")
val report = analyze_sspec_text("test/a_spec.spl",
    "describe \"cache\":\n    it \"has no oracle\":\n        pass_todo\n")
expect(render_json_report_fragments([render_json_report(report)])).to_equal(
    render_json_reports([report]))
expect(render_sarif_result_fragments([
    render_sarif_results_fragment(report)])).to_equal(
    render_sarif_reports([report]))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sspec_maintain/cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSpec per-pair cache identity.
- SSpec per-pair cache identity

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

- Canonical SPipe generation for source `f43745c44122e1cf983ce982352de3e0f2d6885a1de674d289fdfe5a5b412386`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f43745c44122e1cf983ce982352de3e0f2d6885a1de674d289fdfe5a5b412386`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f43745c44122e1cf983ce982352de3e0f2d6885a1de674d289fdfe5a5b412386`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/sspec_maintain/cache_spec.spl
mirror: doc/06_spec/01_unit/app/sspec_maintain/cache_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/sspec_maintain/cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/sspec_maintain/cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/sspec_maintain/cache_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses an unchanged source and manual pair' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sspec_maintain/cache_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates create edit delete move and rename independently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sspec_maintain/cache_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates manual path content rule configuration and tool changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
