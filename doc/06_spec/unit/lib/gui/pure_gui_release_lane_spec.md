# Pure Gui Release Lane Specification

## Scenarios

### pure GUI release lane

#### rejects hosted BrowserWindow and content web sources

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has_forbidden_release_dependency(_existing_source("src/lib/gui/entity/browser_window.spl"))).to_equal(true)
```

</details>

#### rejects Skia-backed hosted presentation sources

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has_forbidden_release_dependency(_existing_source("src/lib/gui/entity/printing.spl"))).to_equal(true)
```

</details>

#### keeps pure GUI release entry surface free of WM, web renderer, Skia, and native GUI runtime deps

1.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/lib/gui/pure_release.spl")
```

</details>

#### keeps pure GUI command boundary free of WM, web renderer, and native GUI runtime deps

1.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/lib/gui/pure_core.spl")
```

</details>

#### keeps pure GUI SMF dynlib perf contract free of WM, web renderer, and native GUI runtime deps

1.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/lib/gui/pure_smf_dynlib_perf.spl")
```

</details>

#### keeps GUI SMF dynlib probe free of WM, web renderer, and native GUI runtime deps

1.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/app/gui_perf/smf_dynlib_probe_core.spl")
```

</details>

#### keeps macOS SMF evidence runner free of WM, web renderer, and native GUI runtime deps

1.  expect release clean

2.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_evidence_core.spl")
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_evidence.spl")
```

</details>

#### keeps QEMU ARM64 SMF parity evidence free of WM, web renderer, and native GUI runtime deps

1.  expect release clean

2.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_parity.spl")
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_parity_evidence.spl")
```

</details>

#### keeps SMF wrapper and exported hot symbol free of WM, web renderer, and native GUI runtime deps

1.  expect release clean

2.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/app/gui_perf/smf_wrap_host_dynlib.spl")
_expect_release_clean("src/app/gui_perf/pure_gui_hot_dynlib_export.spl")
```

</details>

#### keeps BrowserWindow entity free of native GUI runtime deps

1.  expect no native gui runtime


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_no_native_gui_runtime("src/lib/gui/entity/browser_window.spl")
```

</details>

#### keeps Menu entity free of native GUI runtime deps

1.  expect no native gui runtime


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_no_native_gui_runtime("src/lib/gui/entity/menu.spl")
```

</details>

#### keeps IME entity free of native GUI runtime deps

1.  expect no native gui runtime


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_no_native_gui_runtime("src/lib/gui/entity/ime.spl")
```

</details>

#### keeps Printing entity free of native GUI runtime deps

1.  expect no native gui runtime


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_no_native_gui_runtime("src/lib/gui/entity/printing.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gui/pure_gui_release_lane_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pure GUI release lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

