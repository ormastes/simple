# Base64url Encode Fused Perf Specification

> Tests covering fused Base64URL encoder work.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base64url Encode Fused Perf Specification

## Scenarios

### fused Base64URL encoder work

#### uses one exact URL output buffer without a standard-Base64 rescan

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses one exact URL output buffer without a standard-Base64 rescan


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("uses one exact URL output buffer without a standard-Base64 rescan")
val source = file_read("src/lib/common/base_encoding/base64.spl")
expect(source).to_contain("fn _base64url_encode_raw(bytes: [u8]) -> [u8]")
expect(source).to_contain("var out_bytes: [u8] = [0u8; out_len]")
expect(source).to_contain("_bytes_to_text(_base64url_encode_raw(data.bytes()))")
expect(source).to_contain("_bytes_to_text(_base64url_encode_raw(data))")
expect(source).to_not_contain("fn _std_b64_to_url(")
expect(source).to_not_contain("_std_b64_to_url(_base64_encode")
```

</details>

#### preserves RFC tails and has bounded encoder-only N-to-2N scaling

- preserves RFC tails and has bounded encoder-only N-to-2N scaling
   - Expected: base64url_encode("") equals ``
   - Expected: base64url_encode("f") equals `Zg`
   - Expected: base64url_encode("fo") equals `Zm8`
   - Expected: base64url_encode("foo") equals `Zm9v`
   - Expected: small_checksum equals `43696`
   - Expected: large_checksum equals `87384`
   - Expected: base64url_decode(small_encoded) equals `small`
   - Expected: base64url_decode(large_encoded) equals `large`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("preserves RFC tails and has bounded encoder-only N-to-2N scaling")
expect(base64url_encode("")).to_equal("")
expect(base64url_encode("f")).to_equal("Zg")
expect(base64url_encode("fo")).to_equal("Zm8")
expect(base64url_encode("foo")).to_equal("Zm9v")

val small = [for _ in 0..4096: "a"].join("")
val large = [for _ in 0..8192: "a"].join("")
var small_checksum = 0
var large_checksum = 0
val small_start = time_now_unix_micros()
for _ in 0..8:
    small_checksum = small_checksum + base64url_encode(small).len()
val small_us = time_now_unix_micros() - small_start
val large_start = time_now_unix_micros()
for _ in 0..8:
    large_checksum = large_checksum + base64url_encode(large).len()
val large_us = time_now_unix_micros() - large_start

val small_encoded = base64url_encode(small)
val large_encoded = base64url_encode(large)
print "base64url_fused_scaling small_us={small_us} large_us={large_us} small_bytes={small_encoded.len()} large_bytes={large_encoded.len()}"
expect(small_checksum).to_equal(43696)
expect(large_checksum).to_equal(87384)
expect(base64url_decode(small_encoded)).to_equal(small)
expect(base64url_decode(large_encoded)).to_equal(large)
expect(large_us).to_be_less_than(small_us * 3 + 5000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/05_perf/lib/base64url_encode_fused_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering fused Base64URL encoder work.
- fused Base64URL encoder work

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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `034661fecec85b2eee74835b01f124b0e4194f21b61d571361979d74b6cc6698`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `034661fecec85b2eee74835b01f124b0e4194f21b61d571361979d74b6cc6698`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `034661fecec85b2eee74835b01f124b0e4194f21b61d571361979d74b6cc6698`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/05_perf/lib/base64url_encode_fused_perf_spec.spl
mirror: doc/06_spec/05_perf/lib/base64url_encode_fused_perf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/lib/base64url_encode_fused_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/lib/base64url_encode_fused_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/lib/base64url_encode_fused_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/lib/base64url_encode_fused_perf_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses one exact URL output buffer without a standard-Base64 rescan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/lib/base64url_encode_fused_perf_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves RFC tails and has bounded encoder-only N-to-2N scaling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
