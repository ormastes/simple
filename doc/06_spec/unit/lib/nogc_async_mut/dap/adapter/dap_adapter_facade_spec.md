# Dap Adapter Facade Specification

> Tests covering nogc_async_mut dap adapter facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dap Adapter Facade Specification

## Scenarios

### nogc_async_mut dap adapter facade

#### re-exports adapter config and capabilities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports adapter config and capabilities
   - Expected: cfg.adapter_type equals `gdb`
   - Expected: cfg.port equals `3333`
   - Expected: AdapterCapabilities.basic().supports_memory is false
   - Expected: AdapterCapabilities.basic().with_memory().supports_memory is true
   - Expected: lldb_config("app.spl").adapter_type equals `lldb-dap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports adapter config and capabilities")
val cfg = AdapterConfig.gdb("localhost", 3333, "kernel.elf")
expect(cfg.adapter_type).to_equal("gdb")
expect(cfg.port).to_equal(3333)
expect(AdapterCapabilities.basic().supports_memory).to_equal(false)
expect(AdapterCapabilities.basic().with_memory().supports_memory).to_equal(true)
expect(lldb_config("app.spl").adapter_type).to_equal("lldb-dap")
```

</details>

#### re-exports DAP framing and JSON helpers

- re-exports DAP framing and JSON helpers
   - Expected: dap_encode("{}") equals `Content-Length: 2\r\n\r\n{}`
   - Expected: dap_parse_content_length("Content-Length: 17") equals `17`
   - Expected: json_get_text(json, "name") equals `main`
   - Expected: json_get_bool(json, "ok") is true
   - Expected: json_get_int(json, "line") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports DAP framing and JSON helpers")
expect(dap_encode("{}")).to_equal("Content-Length: 2\r\n\r\n{}")
expect(dap_parse_content_length("Content-Length: 17")).to_equal(17)
expect(dap_request(3, "launch", "{}")).to_contain("\"command\":\"launch\"")
val json = "{\"name\":\"main\",\"ok\":true,\"line\":42}"
expect(json_get_text(json, "name")).to_equal("main")
expect(json_get_bool(json, "ok")).to_equal(true)
expect(json_get_int(json, "line")).to_equal(42)
```

</details>

#### re-exports stlink parsing helpers

- re-exports stlink parsing helpers
   - Expected: parse_hex("10") equals `16`
   - Expected: parse_stlink_hex_dump("01 0f 10")[2] equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports stlink parsing helpers")
expect(parse_hex("10")).to_equal(16)
expect(parse_stlink_hex_dump("01 0f 10")[2]).to_equal(16)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut dap adapter facade.
- nogc_async_mut dap adapter facade

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89a79135a538d8c9342c32f618927833c8cdf924caaaa929542a2e9dcab1c737`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89a79135a538d8c9342c32f618927833c8cdf924caaaa929542a2e9dcab1c737`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89a79135a538d8c9342c32f618927833c8cdf924caaaa929542a2e9dcab1c737`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports adapter config and capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports DAP framing and JSON helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports stlink parsing helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
