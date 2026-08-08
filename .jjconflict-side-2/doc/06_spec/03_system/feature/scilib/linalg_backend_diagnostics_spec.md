# Linalg Backend Diagnostics Specification

> 1. fail

<!-- sdn-diagram:id=linalg_backend_diagnostics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linalg_backend_diagnostics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linalg_backend_diagnostics_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linalg_backend_diagnostics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg Backend Diagnostics Specification

## Scenarios

### linalg backend diagnostics

#### reports the configured backend without requiring native libraries

1. fail
   - Expected: required.selected equals `pytorch`
   - Expected: name equals `status.requested`
2. fail
   - Expected: status.selected equals `scalar`
   - Expected: status.available is true
   - Expected: required.selected equals `openblas`
   - Expected: name equals `openblas`
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = linalg_backend_status()
if status.requested == "mock":
    expect(status.selected).to_equal("mock")
    expect(status.available).to_equal(true)
    expect(status.real_native).to_equal(false)
if status.requested == "cuda":
    match require_linalg_backend("cuda"):
        case Ok(required):
            expect(required.selected).to_equal("cuda")
        case Err(BackendError.BackendUnavailable(name)):
            expect(name).to_equal("cuda")
        case _:
            fail("unexpected checked result branch")
if status.requested == "torch" or status.requested == "pytorch":
    match require_linalg_backend(status.requested):
        case Ok(required):
            expect(required.selected).to_equal("pytorch")
        case Err(BackendError.BackendUnavailable(name)):
            expect(name).to_equal(status.requested)
        case _:
            fail("unexpected checked result branch")
if status.requested == "auto":
    expect(status.selected).to_equal("scalar")
    expect(status.available).to_equal(true)
if status.requested == "openblas":
    match require_linalg_backend("openblas"):
        case Ok(required):
            expect(required.selected).to_equal("openblas")
        case Err(BackendError.BackendUnavailable(name)):
            expect(name).to_equal("openblas")
        case _:
            fail("unexpected checked result branch")
```

</details>

#### returns typed unavailable errors for optional accelerator backends

1. fail
   - Expected: name equals `cuda`
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val openblas = require_linalg_backend("openblas")
match openblas:
    case Ok(status):
        expect(status.selected).to_equal("openblas")
        expect(status.available).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        fail("unexpected checked result branch")

val cuda = require_linalg_backend("cuda")
match cuda:
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        fail("unexpected checked result branch")
```

</details>

#### returns typed missing-symbol errors for backend symbol probes

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = check_linalg_symbol("mock", "rt_blas_dgemm", false)
match missing:
    case Err(BackendError.MissingRuntimeSymbol(symbol)):
        expect(symbol).to_equal("rt_blas_dgemm")
    case _:
        fail("unexpected checked result branch")
```

</details>

#### returns typed unsupported errors for unknown backend names

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unknown = require_linalg_backend("not-a-backend")
match unknown:
    case Err(BackendError.UnsupportedBackend(name)):
        expect(name).to_equal("not-a-backend")
    case _:
        fail("unexpected checked result branch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/linalg_backend_diagnostics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- linalg backend diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
