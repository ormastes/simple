# Chunked Size Overflow Sync Specification

> Tests covering nogc_sync_mut http.headers decode_chunked — chunk-size overflow, nogc_sync_mut http1 decode_chunked_with_trailers — chunk-size overflow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chunked Size Overflow Sync Specification

## Scenarios

### nogc_sync_mut http.headers decode_chunked — chunk-size overflow

#### rejects a 2^64 chunk-size instead of reading it as a last-chunk

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a 2^64 chunk-size instead of reading it as a last-chunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a 2^64 chunk-size instead of reading it as a last-chunk")
match decode_chunked("10000000000000000\r\nX\r\n\r\n"):
    case Ok(_):
        assert_true(false)
    case Err(err):
        assert_false(err.is_empty())
```

</details>

#### rejects a 2^64+5 chunk-size instead of wrapping it to 5

- rejects a 2^64+5 chunk-size instead of wrapping it to 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a 2^64+5 chunk-size instead of wrapping it to 5")
match decode_chunked("10000000000000005\r\nABCDE\r\n0\r\n\r\n"):
    case Ok(_):
        assert_true(false)
    case Err(err):
        assert_false(err.is_empty())
```

</details>

#### still decodes a normal terminated stream

- still decodes a normal terminated stream
   - Expected: b equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still decodes a normal terminated stream")
match decode_chunked("5\r\nhello\r\n0\r\n\r\n"):
    case Ok(b):
        expect(b).to_equal("hello")
    case Err(_):
        assert_true(false)
```

</details>

#### still accepts a size padded with leading zeros

- still accepts a size padded with leading zeros
   - Expected: b equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still accepts a size padded with leading zeros")
match decode_chunked("0000000000000000005\r\nhello\r\n0\r\n\r\n"):
    case Ok(b):
        expect(b).to_equal("hello")
    case Err(_):
        assert_true(false)
```

</details>

### nogc_sync_mut http1 decode_chunked_with_trailers — chunk-size overflow

#### rejects a 2^64 chunk-size instead of reading it as a last-chunk

- rejects a 2^64 chunk-size instead of reading it as a last-chunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a 2^64 chunk-size instead of reading it as a last-chunk")
match decode_chunked_with_trailers("10000000000000000\r\nX\r\n\r\n"):
    case Ok(_):
        assert_true(false)
    case Err(err):
        assert_false(err.is_empty())
```

</details>

#### rejects a 2^64+5 chunk-size instead of wrapping it to 5

- rejects a 2^64+5 chunk-size instead of wrapping it to 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a 2^64+5 chunk-size instead of wrapping it to 5")
match decode_chunked_with_trailers("10000000000000005\r\nABCDE\r\n0\r\n\r\n"):
    case Ok(_):
        assert_true(false)
    case Err(err):
        assert_false(err.is_empty())
```

</details>

#### still decodes a normal terminated stream

- still decodes a normal terminated stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still decodes a normal terminated stream")
match decode_chunked_with_trailers("5\r\nhello\r\n0\r\n\r\n"):
    case Ok(data):
        assert_true(data.len() > 0)
    case Err(_):
        assert_true(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http/chunked_size_overflow_sync_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_sync_mut http.headers decode_chunked — chunk-size overflow, nogc_sync_mut http1 decode_chunked_with_trailers — chunk-size overflow.
- nogc_sync_mut http.headers decode_chunked — chunk-size overflow
- nogc_sync_mut http1 decode_chunked_with_trailers — chunk-size overflow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `713c84e4651d4aea63112fbbd87e2f94a065d644facfcd2306c19f6cf2cf9cc1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `713c84e4651d4aea63112fbbd87e2f94a065d644facfcd2306c19f6cf2cf9cc1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `713c84e4651d4aea63112fbbd87e2f94a065d644facfcd2306c19f6cf2cf9cc1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/http/chunked_size_overflow_sync_spec.spl
mirror: doc/06_spec/01_unit/lib/http/chunked_size_overflow_sync_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http/chunked_size_overflow_sync_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http/chunked_size_overflow_sync_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http/chunked_size_overflow_sync_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a 2^64 chunk-size instead of reading it as a last-chunk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http/chunked_size_overflow_sync_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a 2^64+5 chunk-size instead of wrapping it to 5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http/chunked_size_overflow_sync_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still decodes a normal terminated stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
