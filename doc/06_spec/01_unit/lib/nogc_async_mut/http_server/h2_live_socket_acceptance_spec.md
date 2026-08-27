# HTTP/2 live loopback acceptance and deterministic robustness gate

> Uses a real kernel TCP loopback socket and the production pure-Simple

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTTP/2 live loopback acceptance and deterministic robustness gate

Uses a real kernel TCP loopback socket and the production pure-Simple

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Uses a real kernel TCP loopback socket and the production pure-Simple
`H2Connection` wire consumer.  The fixture is deliberately single-process and
bounded: no external h2 client, network service, random source, or sleep is
required.  Failures return an empty receipt and therefore fail the concrete
wire assertions below.

## Scenarios

### HTTP/2 pure-Simple live socket acceptance

#### multiplexes a valid request through one-byte socket fragmentation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- multiplexes a valid request through one-byte socket fragmentation
   - Expected: receipt.request_count equals `1`
   - Expected: receipt.request_path equals `/`
   - Expected: receipt.retained_bytes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("multiplexes a valid request through one-byte socket fragmentation")
val receipt = live_exchange(valid_get_wire(), 1)
expect(receipt.connected).to_be(true)
expect(receipt.request_count).to_equal(1)
expect(receipt.request_path).to_equal("/")
expect(receipt.retained_bytes).to_equal(0)
expect(receipt.goaway).to_be(false)
val wire_text = bytes_to_text(receipt.outbound)
expect(wire_text).to_contain(H2_LIVE_BODY)
expect(wire_text).to_contain("x-content-type-options")
expect(wire_text).to_contain("nosniff")
expect(wire_text).to_contain("x-frame-options")
expect(wire_text).to_contain("DENY")
```

</details>

#### rejects a forbidden zero WINDOW_UPDATE over a live socket

- rejects a forbidden zero WINDOW_UPDATE over a live socket
   - Expected: receipt.request_count equals `0`
   - Expected: receipt.retained_bytes equals `0`
   - Expected: receipt.outbound.len() equals `17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a forbidden zero WINDOW_UPDATE over a live socket")
var wire = h2_connection_preface_bytes()
append_bytes(wire, [0, 0, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0])
val receipt = live_exchange(wire, 3)
expect(receipt.connected).to_be(true)
expect(receipt.request_count).to_equal(0)
expect(receipt.goaway).to_be(true)
expect(receipt.retained_bytes).to_equal(0)
expect(receipt.outbound.len()).to_equal(17)
```

</details>

#### fuzzes deterministic bounded frame declarations without retention growth

- fuzzes deterministic bounded frame declarations without retention growth
   - Expected: receipt.request_count equals `0`
   - Expected: receipt.retained_bytes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fuzzes deterministic bounded frame declarations without retention growth")
var seed: i64 = 731
var case_index = 0
while case_index < 32:
    seed = (seed * 1103515245 + 12345) & 2147483647
    var wire = h2_connection_preface_bytes()
    # Unknown extension types must be ignored while the declared
    # payload is fully present. Payload stays deterministically <= 31.
    val payload_len = seed % 32
    append_bytes(wire, [0, 0, payload_len, 10 + seed % 240, seed % 256, 0, 0, 0, 0])
    var j = 0
    while j < payload_len:
        seed = (seed * 1103515245 + 12345) & 2147483647
        wire.push(seed % 256)
        j = j + 1
    val receipt = live_exchange(wire, 1 + case_index % 7)
    expect(receipt.connected).to_be(true)
    expect(receipt.request_count).to_equal(0)
    expect(receipt.retained_bytes).to_equal(0)
    expect(receipt.retained_bytes).to_be_less_than(H2_MAX_RECV_BUFFER + 1)
    case_index = case_index + 1
```

</details>

#### soaks repeated live connections with bounded latency and RSS

- soaks repeated live connections with bounded latency and RSS
   - Expected: receipt.request_count equals `1`
   - Expected: receipt.retained_bytes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("soaks repeated live connections with bounded latency and RSS")
var elapsed_samples: [i64] = []
var i = 0
while i < 40:
    val receipt = live_exchange(valid_get_wire(), 1 + i % 13)
    expect(receipt.connected).to_be(true)
    expect(receipt.request_count).to_equal(1)
    expect(receipt.retained_bytes).to_equal(0)
    elapsed_samples.push(receipt.elapsed_us)
    i = i + 1
elapsed_samples.sort()
# Nearest-rank p95: ceil(40 * .95) - 1 = 37. A generous CI bound
# catches stalls/deadlocks rather than benchmarking scheduler noise.
expect(elapsed_samples[37]).to_be_less_than(1000001)
val rss_kib = peak_rss_kib()
expect(rss_kib).to_be_greater_than(0)
expect(rss_kib).to_be_less_than(393217)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c8d44c8448cc9bdb8a0d4c198d0327a8d4f0ebc1b54d7960f720f47b36ade0d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c8d44c8448cc9bdb8a0d4c198d0327a8d4f0ebc1b54d7960f720f47b36ade0d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c8d44c8448cc9bdb8a0d4c198d0327a8d4f0ebc1b54d7960f720f47b36ade0d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiplexes a valid request through one-byte socket fragmentation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.spl:187:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a forbidden zero WINDOW_UPDATE over a live socket' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/h2_live_socket_acceptance_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fuzzes deterministic bounded frame declarations without retention growth' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
