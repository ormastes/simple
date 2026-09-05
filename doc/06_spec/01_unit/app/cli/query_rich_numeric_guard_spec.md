# Query Rich Numeric Guard Specification

> Tests covering query rich numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Rich Numeric Guard Specification

## Scenarios

### query rich numeric guard

#### maps source files before the lightweight query parser consumes them

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps source files before the lightweight query parser consumes them
   - Expected: query_file_write(tmp, "fn probe():\n    42\n") is true
   - Expected: query_file_exists(tmp) is true
   - Expected: query_file_read_rich(tmp) equals `fn probe():\n    42\n`
   - Expected: query_file_write(tmp, "héllo wörld") is true
   - Expected: query_file_read_rich(tmp) equals `héllo wörld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps source files before the lightweight query parser consumes them")
# oracle: the mapped read must return the exact bytes written, including
# newlines and non-ASCII payload, for the parser boundary to be correct.
val tmp = "/tmp/query_rich_numeric_guard_probe.txt"
expect(query_file_write(tmp, "fn probe():\n    42\n")).to_equal(true)
expect(query_file_exists(tmp)).to_equal(true)
expect(query_file_read_rich(tmp)).to_equal("fn probe():\n    42\n")
# oracle: unicode payload survives the mmap read
expect(query_file_write(tmp, "héllo wörld")).to_equal(true)
expect(query_file_read_rich(tmp)).to_equal("héllo wörld")
```

</details>

#### defaults malformed rich query coordinates

- defaults malformed rich query coordinates
   - Expected: query_rich_nonnegative_int_or_zero("notanumber") equals `0`
   - Expected: query_rich_nonnegative_int_or_zero("") equals `0`
   - Expected: query_rich_nonnegative_int_or_zero("   ") equals `0`
   - Expected: query_rich_nonnegative_int_or_zero("-5") equals `0`
   - Expected: query_rich_nonnegative_int_or_zero("12a34") equals `0`
   - Expected: query_rich_nonnegative_int_or_zero("128") equals `128`
   - Expected: query_rich_nonnegative_int_or_zero("  77 ") equals `77`
   - Expected: query_rich_nonnegative_int_or_zero("0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults malformed rich query coordinates")
# oracle: any non-digit text, empty text, or negative number must coerce to 0
expect(query_rich_nonnegative_int_or_zero("notanumber")).to_equal(0)
expect(query_rich_nonnegative_int_or_zero("")).to_equal(0)
expect(query_rich_nonnegative_int_or_zero("   ")).to_equal(0)
expect(query_rich_nonnegative_int_or_zero("-5")).to_equal(0)
expect(query_rich_nonnegative_int_or_zero("12a34")).to_equal(0)
# oracle: well-formed decimal text parses exactly, surrounding whitespace trimmed
expect(query_rich_nonnegative_int_or_zero("128")).to_equal(128)
expect(query_rich_nonnegative_int_or_zero("  77 ")).to_equal(77)
expect(query_rich_nonnegative_int_or_zero("0")).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_rich_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering query rich numeric guard.
- query rich numeric guard

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37bbaf2d509387e837cc609ebc89acd11c5ca78ef2abf9ef49d12df8324c2305`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37bbaf2d509387e837cc609ebc89acd11c5ca78ef2abf9ef49d12df8324c2305`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37bbaf2d509387e837cc609ebc89acd11c5ca78ef2abf9ef49d12df8324c2305`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/cli/query_rich_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/cli/query_rich_numeric_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/query_rich_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/query_rich_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/query_rich_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/query_rich_numeric_guard_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps source files before the lightweight query parser consumes them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/query_rich_numeric_guard_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults malformed rich query coordinates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
