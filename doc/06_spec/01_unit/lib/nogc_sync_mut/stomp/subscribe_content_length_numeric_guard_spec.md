# subscribe_content_length_numeric_guard_spec

> Regression guard for STOMP `content-length` parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# subscribe_content_length_numeric_guard_spec

Regression guard for STOMP `content-length` parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression guard for STOMP `content-length` parsing.

History: this guard used to require `return value.to_int() ?? nil`. That
pattern is DEAD -- `.to_int()` is typed `i64?` but its runtime cannot produce
nil, so the `??` arm never fired and `content-length:abc` read as 0.
`subscribe.spl` returns `try_parse_int(value)`, which really can report
failure, and a non-numeric header is treated as the protocol error it is.

## Scenarios

### nogc sync stomp content length numeric guard

### numeric header values parse to their integer value

#### parses numeric content-length values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
expect(try_parse_int("128")).to_equal(128)  # oracle: 128 is the literal header value
expect(try_parse_int("0")).to_equal(0)  # oracle: zero is a valid length
```

</details>

### non-numeric headers must be a reportable failure, never 0

#### reports failure for non-numeric content-length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
expect(try_parse_int("abc") == nil).to_equal(true)
expect(try_parse_int("") == nil).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `9fd7a0b0afb14946eb776f19a5e2de4899ae7da3193315139ae38bcbf9356054`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fd7a0b0afb14946eb776f19a5e2de4899ae7da3193315139ae38bcbf9356054`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fd7a0b0afb14946eb776f19a5e2de4899ae7da3193315139ae38bcbf9356054`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.spl:21:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses numeric content-length values' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/stomp/subscribe_content_length_numeric_guard_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports failure for non-numeric content-length' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
