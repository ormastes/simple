# Wine Posix Adapter Specification

> <details>

<!-- sdn-diagram:id=wine_posix_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_posix_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_posix_adapter_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_posix_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Posix Adapter Specification

## Scenarios

### Wine POSIX adapter contract

#### lists fd, process, stdio, wait, timer, socket, path, and errno APIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apis = wine_posix_adapter_required_apis()
expect(apis.len()).to_be_greater_than(15)
expect(apis[0]).to_equal("fd-open")
```

</details>

#### reports the first missing adapter API

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = wine_posix_adapter_missing_apis("fd-open fd-read fd-write fd-close")
expect(missing[0]).to_equal("fd-dup")
```

</details>

#### maps blocking-compatible adapter APIs onto nogc async primitives

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_posix_adapter_async_binding("fd-read")).to_equal("submit-read")
expect(wine_posix_adapter_async_binding("poll-wait")).to_contain("register-fd")
expect(wine_posix_adapter_async_binding("socket")).to_contain("event-loop")
```

</details>

#### derives POSIX gate features from concrete adapter APIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = wine_posix_adapter_feature_string(_all_adapter_apis())
expect(features).to_contain("fd-table")
expect(features).to_contain("cwd-env-argv")
expect(features).to_contain("spawn")
```

</details>

#### blocks readiness when async completion polling is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_posix_adapter_gate(_all_adapter_apis(), "io-driver submit-open submit-read submit-write submit-close submit-timeout")
expect(result.ready).to_equal(false)
expect(result.state).to_equal("blocked-async-io:missing-poll-completion")
```

</details>

#### accepts the full adapter API set on a nogc async backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_posix_adapter_gate(_all_adapter_apis(), _all_async_features())
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.async_state).to_equal("ready")
```

</details>

#### requires bounded KERNEL32 file I/O evidence before full adapter readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_result = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\hello.txt", 5)
val result = wine_posix_adapter_gate_with_file_io_result(_all_adapter_apis(), _all_async_features(), file_result)
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.posix_features).to_contain("kernel32-file-io")
```

</details>

#### keeps POSIX readiness blocked on failed file I/O bridge evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_result = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\missing.txt", 5)
val result = wine_posix_adapter_gate_with_file_io_result(_all_adapter_apis(), _all_async_features(), file_result)
expect(result.ready).to_equal(false)
expect(result.state).to_equal("file-io-CreateFileW:file-not-found")
```

</details>

#### normalizes host errno values used by Wine compatibility shims

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_posix_adapter_errno_name(2)).to_equal("ENOENT")
expect(wine_posix_adapter_errno_name(11)).to_equal("EAGAIN")
expect(wine_posix_adapter_errno_name(9999)).to_equal("EUNKNOWN")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_posix_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine POSIX adapter contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
