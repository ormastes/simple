# Http H3 Facade Specification

> Tests covering gc_async_mut http h3 facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Http H3 Facade Specification

## Scenarios

### gc_async_mut http h3 facade

#### re-exports varint and frame helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports varint and frame helpers
   - Expected: encoded.length() equals `2`
   - Expected: ok.value equals `64`
   - Expected: ok.consumed equals `2`
   - Expected: msg equals ``
   - Expected: ok.frame_type equals `H3_FRAME_DATA`
   - Expected: ok.payload.length() equals `2`
   - Expected: msg equals ``
   - Expected: H3_FRAME_SETTINGS equals `4`
   - Expected: H3_SETTINGS_MAX_FIELD_SECTION_SIZE equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports varint and frame helpers")
val encoded = h3_varint_encode(64)
expect(encoded.length()).to_equal(2)
match h3_varint_decode(encoded, 0):
    case Ok(ok):
        expect(ok.value).to_equal(64)
        expect(ok.consumed).to_equal(2)
    case Err(msg):
        expect(msg).to_equal("")

val frame = h3_frame_emit(H3_FRAME_DATA, [1 as u8, 2 as u8])
match h3_frame_parse(frame, 0):
    case Ok(ok):
        expect(ok.frame_type).to_equal(H3_FRAME_DATA)
        expect(ok.payload.length()).to_equal(2)
    case Err(msg):
        expect(msg).to_equal("")

expect(H3_FRAME_SETTINGS).to_equal(4)
expect(H3_SETTINGS_MAX_FIELD_SECTION_SIZE).to_equal(6)
```

</details>

#### re-exports QPACK static table helpers

- re-exports QPACK static table helpers
   - Expected: qpack_static_table().length() equals `99`
   - Expected: qpack_static_lookup(25).value equals `200`
   - Expected: qpack_static_find_name(":method") equals `15`
   - Expected: qpack_static_find_exact(":status", "404") equals `27`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports QPACK static table helpers")
expect(qpack_static_table().length()).to_equal(99)
expect(qpack_static_lookup(25).value).to_equal("200")
expect(qpack_static_find_name(":method")).to_equal(15)
expect(qpack_static_find_exact(":status", "404")).to_equal(27)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut http h3 facade.
- gc_async_mut http h3 facade

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

- Canonical SPipe generation for source `728239fa6ea02b7076bea96429a4bc0a7a7ca8a93d31a40bd40a66f1f8fa1a52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `728239fa6ea02b7076bea96429a4bc0a7a7ca8a93d31a40bd40a66f1f8fa1a52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `728239fa6ea02b7076bea96429a4bc0a7a7ca8a93d31a40bd40a66f1f8fa1a52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports varint and frame helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports QPACK static table helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
