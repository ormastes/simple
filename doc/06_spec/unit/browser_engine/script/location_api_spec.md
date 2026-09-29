# Location Api Specification

> Tests covering Browser script location API, Location.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Location Api Specification

## Scenarios

### Browser script location API

### Location

#### parses URL fields

- parses URL fields
   - Expected: loc.href equals `https://example.test/path/page?q=1#top`
   - Expected: loc.protocol equals `https:`
   - Expected: loc.host equals `example.test`
   - Expected: loc.pathname equals `/path/page`
   - Expected: loc.search equals `?q=1`
   - Expected: loc.hash equals `#top`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses URL fields")
val loc = location_from_url("https://example.test/path/page?q=1#top")
expect(loc.href).to_equal("https://example.test/path/page?q=1#top")
expect(loc.protocol).to_equal("https:")
expect(loc.host).to_equal("example.test")
expect(loc.pathname).to_equal("/path/page")
expect(loc.search).to_equal("?q=1")
expect(loc.hash).to_equal("#top")
```

</details>

#### parses search without hash

- parses search without hash
   - Expected: loc.protocol equals `http:`
   - Expected: loc.host equals `other.test`
   - Expected: loc.pathname equals `/next`
   - Expected: loc.search equals `?q=2`
   - Expected: loc.hash equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses search without hash")
val loc = location_from_url("http://other.test/next?q=2")
expect(loc.protocol).to_equal("http:")
expect(loc.host).to_equal("other.test")
expect(loc.pathname).to_equal("/next")
expect(loc.search).to_equal("?q=2")
expect(loc.hash).to_equal("")
```

</details>

#### assigns a new location

- assigns a new location
   - Expected: next.href equals `http://other.test/next?q=2`
   - Expected: next.protocol equals `http:`
   - Expected: next.host equals `other.test`
   - Expected: next.pathname equals `/next`
   - Expected: next.search equals `?q=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns a new location")
val loc = location_from_url("https://example.test/start")
val next = location_assign(loc, "http://other.test/next?q=2")
expect(next.href).to_equal("http://other.test/next?q=2")
expect(next.protocol).to_equal("http:")
expect(next.host).to_equal("other.test")
expect(next.pathname).to_equal("/next")
expect(next.search).to_equal("?q=2")
```

</details>

#### reload refreshes parsed fields from current href

- reload refreshes parsed fields from current href
   - Expected: reloaded.href equals `https://example.test/reloaded?q=3#done`
   - Expected: reloaded.protocol equals `https:`
   - Expected: reloaded.host equals `example.test`
   - Expected: reloaded.pathname equals `/reloaded`
   - Expected: reloaded.search equals `?q=3`
   - Expected: reloaded.hash equals `#done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reload refreshes parsed fields from current href")
val loc = location_from_url("https://example.test/start")
loc.href = "https://example.test/reloaded?q=3#done"
val reloaded = location_reload(loc)
expect(reloaded.href).to_equal("https://example.test/reloaded?q=3#done")
expect(reloaded.protocol).to_equal("https:")
expect(reloaded.host).to_equal("example.test")
expect(reloaded.pathname).to_equal("/reloaded")
expect(reloaded.search).to_equal("?q=3")
expect(reloaded.hash).to_equal("#done")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/browser_engine/script/location_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser script location API, Location.
- Browser script location API
- Location

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

- Canonical SPipe generation for source `48ae07247d689fdb8e26f325330ae86e85f128f8695a454832a64e1050f85198`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48ae07247d689fdb8e26f325330ae86e85f128f8695a454832a64e1050f85198`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48ae07247d689fdb8e26f325330ae86e85f128f8695a454832a64e1050f85198`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/browser_engine/script/location_api_spec.spl
mirror: doc/06_spec/unit/browser_engine/script/location_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/script/location_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/script/location_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/script/location_api_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses URL fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/script/location_api_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses search without hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/script/location_api_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns a new location' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
