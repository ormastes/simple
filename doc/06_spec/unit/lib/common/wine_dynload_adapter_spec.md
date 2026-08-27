# Wine Dynload Adapter Specification

> Tests covering Wine dynamic loader adapter contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dynload Adapter Specification

## Scenarios

### Wine dynamic loader adapter contract

#### lists native loader, dependency, namespace, relocation, import, TLS, and error APIs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists native loader, dependency, namespace, relocation, import, TLS, and error APIs
   - Expected: apis[0] equals `native-module-open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists native loader, dependency, namespace, relocation, import, TLS, and error APIs")
val apis = wine_dynload_adapter_required_apis()
expect(apis.len()).to_be_greater_than(10)
expect(apis[0]).to_equal("native-module-open")
```

</details>

#### reports the first missing dynamic loader API

- reports the first missing dynamic loader API
   - Expected: missing[0] equals `search-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing dynamic loader API")
val missing = wine_dynload_adapter_missing_apis(_current_native_loader_apis())
expect(missing[0]).to_equal("search-path")
```

</details>

#### maps existing native dynamic loader bindings

- maps existing native dynamic loader bindings
   - Expected: wine_dynload_adapter_native_binding("native-module-open") equals `spl_dlopen`
   - Expected: wine_dynload_adapter_native_binding("native-symbol-lookup") equals `spl_dlsym`
   - Expected: wine_dynload_adapter_native_binding("native-self-handle") equals `dlopen(NULL)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps existing native dynamic loader bindings")
expect(wine_dynload_adapter_native_binding("native-module-open")).to_equal("spl_dlopen")
expect(wine_dynload_adapter_native_binding("native-symbol-lookup")).to_equal("spl_dlsym")
expect(wine_dynload_adapter_native_binding("native-self-handle")).to_equal("dlopen(NULL)")
```

</details>

#### does not treat native dlopen alone as Wine dynamic-loader readiness

- does not treat native dlopen alone as Wine dynamic-loader readiness
   - Expected: result.ready is false
   - Expected: result.state equals `missing-api-search-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat native dlopen alone as Wine dynamic-loader readiness")
val result = wine_dynload_adapter_gate(_current_native_loader_apis())
expect(result.ready).to_equal(false)
expect(result.state).to_equal("missing-api-search-path")
expect(result.dynload_features).to_contain("dynload")
```

</details>

#### derives Wine dynamic gate features from the full coexistence surface

- derives Wine dynamic gate features from the full coexistence surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives Wine dynamic gate features from the full coexistence surface")
val features = wine_dynload_adapter_feature_string(_all_dynload_apis())
expect(features).to_contain("dynload")
expect(features).to_contain("symbol-lookup")
expect(features).to_contain("loader-errors")
```

</details>

#### accepts the full dynamic loading coexistence API set

- accepts the full dynamic loading coexistence API set
   - Expected: result.ready is true
   - Expected: result.state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the full dynamic loading coexistence API set")
val result = wine_dynload_adapter_gate(_all_dynload_apis())
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
```

</details>

#### requires bounded NTDLL loader resolution evidence before full adapter readiness

- requires bounded NTDLL loader resolution evidence before full adapter readiness
   - Expected: result.ready is true
   - Expected: result.state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires bounded NTDLL loader resolution evidence before full adapter readiness")
val loader = wine_ntdll_execute_loader_resolution(
    ["LdrLoadDll", "LdrGetProcedureAddress", "LdrUnloadDll"],
    wine_ntdll_loader_table_new(),
    "KERNEL32.dll",
    "GetProcAddress"
)
val result = wine_dynload_adapter_gate_with_loader_result(_all_dynload_apis(), loader)
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.dynload_features).to_contain("ntdll-loader-resolution")
```

</details>

#### keeps dynamic-loader readiness blocked on failed loader resolution

- keeps dynamic-loader readiness blocked on failed loader resolution
   - Expected: result.ready is false
   - Expected: result.state equals `loader-resolution-LdrLoadDll:module-not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps dynamic-loader readiness blocked on failed loader resolution")
val loader = wine_ntdll_execute_loader_resolution(
    ["LdrLoadDll", "LdrGetProcedureAddress", "LdrUnloadDll"],
    wine_ntdll_loader_table_new(),
    "advapi32.dll",
    "RegOpenKeyExW"
)
val result = wine_dynload_adapter_gate_with_loader_result(_all_dynload_apis(), loader)
expect(result.ready).to_equal(false)
expect(result.state).to_equal("loader-resolution-LdrLoadDll:module-not-found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_dynload_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine dynamic loader adapter contract.
- Wine dynamic loader adapter contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `b0cd643da36d9dde8d52b1bf5de9fcbf56abf6a5f055228445879d4974804b95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b0cd643da36d9dde8d52b1bf5de9fcbf56abf6a5f055228445879d4974804b95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b0cd643da36d9dde8d52b1bf5de9fcbf56abf6a5f055228445879d4974804b95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/wine_dynload_adapter_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_dynload_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_dynload_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_dynload_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_dynload_adapter_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists native loader, dependency, namespace, relocation, import, TLS, and error APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_dynload_adapter_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing dynamic loader API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_dynload_adapter_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps existing native dynamic loader bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
