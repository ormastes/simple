# Log Default Level Error Visible Specification

> Tests covering nogc_sync_mut log default level.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Default Level Error Visible Specification

## Scenarios

### nogc_sync_mut log default level

#### enables error-level output by default (never LOG_OFF when SIMPLE_LOG is unset)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- enables error-level output by default (never LOG_OFF when SIMPLE_LOG is unset)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("enables error-level output by default (never LOG_OFF when SIMPLE_LOG is unset)")
# In the test environment SIMPLE_LOG is not set to "off"; the pre-fix
# behavior returned 0 (LOG_OFF) here, silencing error() and fatal().
expect(get_log_level() >= LOG_ERROR).to_be_true()
```

</details>

#### keeps the severity ordering that gates emission

- keeps the severity ordering that gates emission
   - Expected: LOG_OFF equals `0`
   - Expected: LOG_FATAL equals `1`
   - Expected: LOG_ERROR equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the severity ordering that gates emission")
expect(LOG_OFF).to_equal(0)
expect(LOG_FATAL).to_equal(1)
expect(LOG_ERROR).to_equal(2)
```

</details>

#### error() and fatal() execute without raising at the default level

- error() and fatal() execute without raising at the default level


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("error() and fatal() execute without raising at the default level")
# Generalization: both severe emitters take the emission path (the one
# the pre-fix default skipped entirely) and must not crash.
error("spec", "regression-guard error line")
fatal("spec", "regression-guard fatal line")
expect(true).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_sync_mut log default level.
- nogc_sync_mut log default level

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `eb280b21cc0c65c140745a1f2268eca417e3cb47ea9ebd97ef4560359652846b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb280b21cc0c65c140745a1f2268eca417e3cb47ea9ebd97ef4560359652846b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb280b21cc0c65c140745a1f2268eca417e3cb47ea9ebd97ef4560359652846b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables error-level output by default (never LOG_OFF when SIMPLE_LOG is unset)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the severity ordering that gates emission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'error() and fatal() execute without raising at the default level' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
