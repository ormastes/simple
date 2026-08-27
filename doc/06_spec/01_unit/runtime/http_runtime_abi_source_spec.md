# Http Runtime Abi Source Specification

> Tests covering native HTTP runtime ABI ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Http Runtime Abi Source Specification

## Scenarios

### native HTTP runtime ABI ownership

#### keeps the tuple-handle GET owner beside request and download

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the tuple-handle GET owner beside request and download
   - Expected: legacy does not contain `rt_http_get(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the tuple-handle GET owner beside request and download")
val legacy = http_abi_source("src/runtime/runtime.c")
val native = http_abi_source("src/runtime/runtime_native.c")
val header = http_abi_source("src/runtime/runtime.h")

expect(legacy.contains("rt_http_get(")).to_equal(false)
expect(native).to_contain("int64_t rt_http_get(int64_t url_value)")
expect(header).to_contain("int64_t  rt_http_get(int64_t url);")
```

</details>

#### routes text-header clients through the canonical array adapter

- routes text-header clients through the canonical array adapter
   - Expected: clients does not contain `extern fn rt_http_request`
   - Expected: clients does not contain `rt_http_request(`
   - Expected: js does not contain `extern fn rt_http_request`
   - Expected: js does not contain `rt_http_request(`
   - Expected: service does not contain `rt_http_get(url: text) -> {text: text}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes text-header clients through the canonical array adapter")
var clients = http_abi_source("src/app/llm_caret/provider.spl")
clients = clients + http_abi_source("src/app/llm_caret/mod.spl")
clients = clients + http_abi_source("src/app/llm_caret/openai_compat.spl")
clients = clients + http_abi_source("src/app/llm_caret/openai_api.spl")
clients = clients + http_abi_source("src/app/llm_caret/claude_api.spl")
clients = clients + http_abi_source("src/app/llm_caret/server.spl")
val js = http_abi_source("src/lib/nogc_sync_mut/js/engine/interpreter.spl")
val service = http_abi_source("src/app/test_daemon/adapters/service_adapter.spl")

expect(clients).to_contain("http_request_raw")
expect(js).to_contain("http_request_raw")
expect(clients.contains("extern fn rt_http_request")).to_equal(false)
expect(clients.contains("rt_http_request(")).to_equal(false)
expect(js.contains("extern fn rt_http_request")).to_equal(false)
expect(js.contains("rt_http_request(")).to_equal(false)
expect(service.contains("rt_http_get(url: text) -> {text: text}")).to_equal(false)
```

</details>

#### keeps seed-library reload on the tuple-handle ABI

- keeps seed-library reload on the tuple-handle ABI
   - Expected: reload does not contain `_rt_http_get(url.ptr(), url.len())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps seed-library reload on the tuple-handle ABI")
val reload = http_abi_source("src/compiler_rust/lib/std/src/tooling/watch/reload.spl")

expect(reload).to_contain("fn _rt_http_get(url: text) -> (i64, text, text)")
expect(reload).to_contain("_rt_http_get(url).1")
expect(reload.contains("_rt_http_get(url.ptr(), url.len())")).to_equal(false)
```

</details>

#### names raw-C-string generator compatibility separately

- names raw-C-string generator compatibility separately
   - Expected: compiler_spec does not contain `unsafe_extern_c("rt_http_get",`
   - Expected: app_spec does not contain `unsafe_extern_c("rt_http_get",`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names raw-C-string generator compatibility separately")
val compiler_spec = http_abi_source("src/compiler/90.tools/sffi_gen/specs/net_mod.spl")
val app_spec = http_abi_source("src/app/ffi_gen.specs/net_mod.spl")

expect(compiler_spec).to_contain("rt_http_get_cstr")
expect(app_spec).to_contain("rt_http_get_cstr")
expect(compiler_spec.contains("unsafe_extern_c(\"rt_http_get\",")).to_equal(false)
expect(app_spec.contains("unsafe_extern_c(\"rt_http_get\",")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/http_runtime_abi_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native HTTP runtime ABI ownership.
- native HTTP runtime ABI ownership

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

- Canonical SPipe generation for source `599716e4361453be314d57d1be4c8d36edc2fd8e12f99dbfe7110937c4877257`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `599716e4361453be314d57d1be4c8d36edc2fd8e12f99dbfe7110937c4877257`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `599716e4361453be314d57d1be4c8d36edc2fd8e12f99dbfe7110937c4877257`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/runtime/http_runtime_abi_source_spec.spl
mirror: doc/06_spec/01_unit/runtime/http_runtime_abi_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/http_runtime_abi_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/http_runtime_abi_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/http_runtime_abi_source_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the tuple-handle GET owner beside request and download' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/http_runtime_abi_source_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes text-header clients through the canonical array adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/http_runtime_abi_source_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps seed-library reload on the tuple-handle ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
