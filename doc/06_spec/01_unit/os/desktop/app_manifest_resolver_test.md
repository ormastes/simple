# App-manifest backend resolution unit manual: scope and evidence

## Purpose and audience

Desktop/runtime maintainers use these nine scenarios to verify the backend
selection policy independently of starting Electron or creating a window.
The matrix covers requested Auto, Electron and SimpleWeb across SimpleOS,
a host without Electron and a host where Electron is available.

## Assumptions and primary workflow

Construct explicit HostCaps values for each host. Auto resolves to SimpleWeb
on SimpleOS or an unavailable-Electron host, and to Electron otherwise.
Explicit Electron returns AppManifestError.ElectronNotAvailable on the first
two hosts and succeeds on the third. Explicit SimpleWeb remains SimpleWeb
on every host. Preserve the rejection assertions rather than accepting any
error or suppressing a failed helper match.

## Traceability and recovery

Source: `test/01_unit/os/desktop/app_manifest_resolver_test.spl`; owner: `src/os/desktop/app_manifest.spl`.
The API declares Result<UiBackendKind, AppManifestError> and the single error
variant ElectronNotAvailable. No new REQ identifier or feature selection is
invented by this existing-fixture synchronization. If resolution fails,
retain requested kind, both capability flags, actual Result variant and error
owner identity before diagnosing policy; do not substitute the obsolete
ManifestError name or broaden a matcher to accept any result.

## Evidence and limitations

Current source SHA256:
`8f832e34963c6787f6f3955108ccb9339c557cf5fde21947ff4c9b81634f5f03`.
Legacy original row23709 passed seven of nine and rejected two examples with
missing-return errors in the helper matching the wrong enum owner. The
changed canonical copy independently passed9/9, zero failed/skipped/pending,
under pinned Phase1 seed0f9bfc1/frozen dependency e59027c, kernel exit0 and
quiescent1. The dated bug records actual receipt paths and exact identities.
This seed diagnostic verifies fixture/API policy synchronization; it does not
qualify native desktop startup, Electron availability detection, or the whole
bootstrap. These tests use explicit capability values and launch no browser.
The generated executable body is retained below; no passing test was replayed.

# App Manifest Resolver Test Specification

> Tests covering app_manifest.resolve_backend / Auto, app_manifest.resolve_backend / Electron, app_manifest.resolve_backend / SimpleWeb.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Manifest Resolver Test Specification

## Scenarios

### app_manifest.resolve_backend / Auto
_Auto picks SimpleWeb unless Electron is available on a non-SimpleOS host._

#### resolves to SimpleWeb on SimpleOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.Auto, host_caps_simpleos())
expect(_is_ok_simple_web(r)).to_equal(true)
```

</details>

#### resolves to SimpleWeb on a host without Electron

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.Auto, host_caps_host(false))
expect(_is_ok_simple_web(r)).to_equal(true)
```

</details>

#### resolves to Electron on a host with Electron available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.Auto, host_caps_host(true))
expect(_is_ok_electron(r)).to_equal(true)
```

</details>

### app_manifest.resolve_backend / Electron
_Explicit Electron only succeeds where Electron is actually available._

#### rejects Electron on SimpleOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.Electron, host_caps_simpleos())
expect(_is_err_electron_not_available(r)).to_equal(true)
```

</details>

#### rejects Electron on a host without Electron

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.Electron, host_caps_host(false))
expect(_is_err_electron_not_available(r)).to_equal(true)
```

</details>

#### accepts Electron on a host where Electron is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.Electron, host_caps_host(true))
expect(_is_ok_electron(r)).to_equal(true)
```

</details>

### app_manifest.resolve_backend / SimpleWeb
_Explicit SimpleWeb is a no-op everywhere._

#### resolves SimpleWeb unchanged on SimpleOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.SimpleWeb, host_caps_simpleos())
expect(_is_ok_simple_web(r)).to_equal(true)
```

</details>

#### resolves SimpleWeb unchanged on a host without Electron

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.SimpleWeb, host_caps_host(false))
expect(_is_ok_simple_web(r)).to_equal(true)
```

</details>

#### resolves SimpleWeb unchanged on a host with Electron

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = resolve_backend(UiBackendKind.SimpleWeb, host_caps_host(true))
expect(_is_ok_simple_web(r)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/app_manifest_resolver_test.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering app_manifest.resolve_backend / Auto, app_manifest.resolve_backend / Electron, app_manifest.resolve_backend / SimpleWeb.
- app_manifest.resolve_backend / Auto
- app_manifest.resolve_backend / Electron
- app_manifest.resolve_backend / SimpleWeb

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
