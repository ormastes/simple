# Native Io Typed U8 Specification

> Tests covering typed u8 native I/O marshalling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Io Typed U8 Specification

## Scenarios

### typed u8 native I/O marshalling

#### sends a genuinely typed u8 payload through UDP

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sends a genuinely typed u8 payload through UDP
   - Expected: bind_err equals `0`
   - Expected: send_err equals `0`
   - Expected: sent equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sends a genuinely typed u8 payload through UDP")
val (fd, bind_err) = native_udp_bind("127.0.0.1:0")
expect(bind_err).to_equal(0)
val payload: [u8] = [1u8, 127u8, 255u8]
val (sent, send_err) = native_udp_send_to(fd, payload, payload.len(), "127.0.0.1:9")
expect(send_err).to_equal(0)
expect(sent).to_equal(payload.len())
native_udp_close(fd)
```

</details>

#### writes a genuinely typed u8 payload through filesystem I/O

- writes a genuinely typed u8 payload through filesystem I/O
   - Expected: written.unwrap() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes a genuinely typed u8 payload through filesystem I/O")
val payload: [u8] = [0u8, 128u8, 255u8]
val written = native_fs_write("/tmp/simple_native_io_typed_u8_spec.bin", payload)
expect(written.unwrap()).to_equal(payload.len())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/native_io_typed_u8_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed u8 native I/O marshalling.
- typed u8 native I/O marshalling

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2e0e1e08e3b0db5e278caf5db4f5a7e9d81f72672438cbabd7bff1de67df4dd3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2e0e1e08e3b0db5e278caf5db4f5a7e9d81f72672438cbabd7bff1de67df4dd3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2e0e1e08e3b0db5e278caf5db4f5a7e9d81f72672438cbabd7bff1de67df4dd3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/compiler/native_io_typed_u8_spec.spl
mirror: doc/06_spec/02_integration/compiler/native_io_typed_u8_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/native_io_typed_u8_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/native_io_typed_u8_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/native_io_typed_u8_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/native_io_typed_u8_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sends a genuinely typed u8 payload through UDP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/native_io_typed_u8_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes a genuinely typed u8 payload through filesystem I/O' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
