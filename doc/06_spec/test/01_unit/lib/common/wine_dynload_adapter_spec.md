# Wine Dynload Adapter Specification

> <details>

<!-- sdn-diagram:id=wine_dynload_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dynload_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dynload_adapter_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dynload_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dynload Adapter Specification

## Scenarios

### Wine dynamic loader adapter contract

#### lists native loader, dependency, namespace, relocation, import, TLS, and error APIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apis = wine_dynload_adapter_required_apis()
expect(apis.len()).to_be_greater_than(10)
expect(apis[0]).to_equal("native-module-open")
```

</details>

#### reports the first missing dynamic loader API

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = wine_dynload_adapter_missing_apis(_current_native_loader_apis())
expect(missing[0]).to_equal("search-path")
```

</details>

#### maps existing native dynamic loader bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_dynload_adapter_native_binding("native-module-open")).to_equal("spl_dlopen")
expect(wine_dynload_adapter_native_binding("native-symbol-lookup")).to_equal("spl_dlsym")
expect(wine_dynload_adapter_native_binding("native-self-handle")).to_equal("dlopen(NULL)")
```

</details>

#### does not treat native dlopen alone as Wine dynamic-loader readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_dynload_adapter_gate(_current_native_loader_apis())
expect(result.ready).to_equal(false)
expect(result.state).to_equal("missing-api-search-path")
expect(result.dynload_features).to_contain("dynload")
```

</details>

#### derives Wine dynamic gate features from the full coexistence surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = wine_dynload_adapter_feature_string(_all_dynload_apis())
expect(features).to_contain("dynload")
expect(features).to_contain("symbol-lookup")
expect(features).to_contain("loader-errors")
```

</details>

#### accepts the full dynamic loading coexistence API set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_dynload_adapter_gate(_all_dynload_apis())
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
```

</details>

#### requires bounded NTDLL loader resolution evidence before full adapter readiness

1. wine ntdll loader table new
   - Expected: result.ready is true
   - Expected: result.state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. wine ntdll loader table new
   - Expected: result.ready is false
   - Expected: result.state equals `loader-resolution-LdrLoadDll:module-not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/common/wine_dynload_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
