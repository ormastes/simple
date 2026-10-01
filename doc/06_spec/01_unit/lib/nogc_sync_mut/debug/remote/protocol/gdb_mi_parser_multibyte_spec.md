# Gdb Mi Parser Multibyte Specification

> Tests covering GdbMiParser multi-byte.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gdb Mi Parser Multibyte Specification

## Scenarios

### GdbMiParser multi-byte

#### café inside an async record's first quoted value does not truncate the record

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- café inside an async record's first quoted value does not truncate the record
   - Expected: cls equals `stopped`
   - Expected: data["reason"] equals `café-hit`
   - Expected: data["value"] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("café inside an async record's first quoted value does not truncate the record")
val r = GdbMiParser.parse_line("*stopped,reason=\"café-hit\",value=\"42\"")
match r:
    GdbMiRecord.Async(cls, data):
        expect(cls).to_equal("stopped")
        expect(data["reason"]).to_equal("café-hit")
        expect(data["value"]).to_equal("42")
    _:
        expect(false).to_be(true)  # wrong record kind
```

</details>

#### CJK content in a result record's first value does not drop later keys

- CJK content in a result record's first value does not drop later keys
   - Expected: cls equals `done`
   - Expected: data["name"] equals `日本語`
   - Expected: data["id"] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CJK content in a result record's first value does not drop later keys")
val r = GdbMiParser.parse_line("^done,name=\"日本語\",id=\"7\"")
match r:
    GdbMiRecord.Result(token, cls, data):
        expect(cls).to_equal("done")
        expect(data["name"]).to_equal("日本語")
        expect(data["id"]).to_equal("7")
    _:
        expect(false).to_be(true)
```

</details>

#### em-dash inside a nested tuple value does not desync the tuple's closing brace

- em-dash inside a nested tuple value does not desync the tuple's closing brace
   - Expected: cls equals `stopped`
   - Expected: data["frame"] equals `{func="a—b",line="5"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("em-dash inside a nested tuple value does not desync the tuple's closing brace")
val r = GdbMiParser.parse_line("*stopped,frame={func=\"a—b\",line=\"5\"}")
match r:
    GdbMiRecord.Async(cls, data):
        expect(cls).to_equal("stopped")
        expect(data["frame"]).to_equal("{func=\"a—b\",line=\"5\"}")
    _:
        expect(false).to_be(true)
```

</details>

#### pure ASCII is unaffected (regression guard)

- pure ASCII is unaffected (regression guard)
   - Expected: cls equals `done`
   - Expected: data["reason"] equals `exited`
   - Expected: data["code"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pure ASCII is unaffected (regression guard)")
val r = GdbMiParser.parse_line("^done,reason=\"exited\",code=\"0\"")
match r:
    GdbMiRecord.Result(token, cls, data):
        expect(cls).to_equal("done")
        expect(data["reason"]).to_equal("exited")
        expect(data["code"]).to_equal("0")
    _:
        expect(false).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GdbMiParser multi-byte.
- GdbMiParser multi-byte

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

- Canonical SPipe generation for source `4a26f20d53039535e0f5a9148772ee994a87e34f6b7800721d90700072c179b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a26f20d53039535e0f5a9148772ee994a87e34f6b7800721d90700072c179b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a26f20d53039535e0f5a9148772ee994a87e34f6b7800721d90700072c179b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'café inside an async record's first quoted value does not truncate the record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CJK content in a result record's first value does not drop later keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'em-dash inside a nested tuple value does not desync the tuple's closing brace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
