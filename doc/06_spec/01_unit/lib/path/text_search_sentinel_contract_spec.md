# DEFECT CLASS: raw i64 sentinel search results must never be matched as Optional

> `text.find`, `text.rfind` and `text.index_of` all return a RAW `i64`: the index on a hit, `-1` on a miss. None of them returns an `Optional`. Consuming one with

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DEFECT CLASS: raw i64 sentinel search results must never be matched as Optional

`text.find`, `text.rfind` and `text.index_of` all return a RAW `i64`: the index on a hit, `-1` on a miss. None of them returns an `Optional`. Consuming one with

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/path/text_search_sentinel_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`text.find`, `text.rfind` and `text.index_of` all return a RAW `i64`: the index
on a hit, `-1` on a miss. None of them returns an `Optional`. Consuming one with

```simple
match haystack.rfind(needle):
    Some(i): ...
    nil: ...
```

is therefore always wrong: the `Some` arm wins unconditionally and binds
`i = -1`, making the `nil` arm dead code and pushing `-1` into arithmetic and
`substring` calls downstream. Row 559's `std.path` bug was one instance; this
file pins the CLASS so a sibling cannot regress the same way.

The correct consumption is an explicit sentinel test (`if i < 0`), which is what
every other stdlib consumer already does (`dependency_tracker/graph.spl`,
`test_runner_execute.spl`, `editor/extensions/contract.spl`,
`web/browser_session.spl`, `blink/layout/block_flow.spl`).

TODO-DB row 559.

## Scenarios

### text search sentinel contract

#### every text search API reports a miss as the raw sentinel -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### matching a sentinel result as Optional does NOT take the nil arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(optional_match_on_sentinel(), -1)
```

</details>

#### no std.path accessor leaks a negative index into its result

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Each of these has a miss on at least one internal rfind.
assert_equal(path.dirname("plain"), ".")
assert_equal(path.extension("plain"), "")
assert_equal(path.stem("plain"), "plain")
assert_equal(path.extension("archive.tar.gz"), "gz")
assert_equal(path.stem("archive.tar.gz"), "archive.tar")
# A leading-dot name has its only dot at index 0: still "no extension".
assert_equal(path.extension(".gitignore"), "")
# A name ending in a dot has the dot at len-1: still "no extension".
assert_equal(path.extension("trailing."), "")
```

</details>

#### positive control: hits are reported at their real indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal("abc".rfind("b"), 1)
assert_equal("abc".index_of("c"), 2)
assert_equal("abcabc".rfind("a"), 3)
assert_equal(path.dirname("/usr/lib/x.so"), "/usr/lib")
assert_equal(path.basename("/usr/lib/x.so"), "x.so")
assert_equal(path.extension("x.so"), "so")
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3bb4ca8ce565fd1f4af0e3eec879bac0ed405eaa4aaf61d3ce149d8240bac125`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3bb4ca8ce565fd1f4af0e3eec879bac0ed405eaa4aaf61d3ce149d8240bac125`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3bb4ca8ce565fd1f4af0e3eec879bac0ed405eaa4aaf61d3ce149d8240bac125`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/path/text_search_sentinel_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/path/text_search_sentinel_contract_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/path/text_search_sentinel_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/path/text_search_sentinel_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/path/text_search_sentinel_contract_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/path/text_search_sentinel_contract_spec.spl:62:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'every text search API reports a miss as the raw sentinel -1' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/path/text_search_sentinel_contract_spec.spl:69:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matching a sentinel result as Optional does NOT take the nil arm' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/path/text_search_sentinel_contract_spec.spl:72:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'no std.path accessor leaks a negative index into its result' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/path/text_search_sentinel_contract_spec.spl:87:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'positive control: hits are reported at their real indices' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
