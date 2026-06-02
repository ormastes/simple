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

2.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/app/gui_perf/smf_dynlib_probe_core.spl")
_expect_release_clean("src/app/gui_perf/smf_dynlib_probe.spl")
```

</details>

#### rejects legacy Rust SMF and dyncall runtime helpers in GUI release sources

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has_forbidden_release_dependency("extern fn rt_file_wrap_smf_dynlib(input: text, output: text, arch: text) -> bool")).to_equal(true)
expect(_has_forbidden_release_dependency("extern fn rt_file_extract_smf_dynlib(input: text, output: text) -> bool")).to_equal(true)
expect(_has_forbidden_release_dependency("extern fn rt_dyncall_0(ptr: i64) -> i64")).to_equal(true)
expect(_has_forbidden_release_dependency("extern fn rt_dyncall_1(ptr: i64, arg0: i64) -> i64")).to_equal(true)
expect(_has_forbidden_release_dependency("extern fn rt_dyncall_6(ptr: i64, a: i64, b: i64, c: i64, d: i64, e: i64, f: i64) -> i64")).to_equal(true)
expect(_has_forbidden_release_dependency("extern fn rt_webgpu_present(surface: i64) -> i64")).to_equal(true)
expect(_has_forbidden_release_dependency("use std.sffi.dynamic.{spl_dlopen, spl_dlsym, spl_dlclose, spl_wffi_call_i64}")).to_equal(false)
```

</details>

#### keeps macOS SMF evidence runner free of WM, web renderer, and native GUI runtime deps

1.  expect release clean

2.  expect release clean

3.  expect release clean

4.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_evidence_core.spl")
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_evidence.spl")
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_transcript_check.spl")
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_release_gate.spl")
```

</details>

#### keeps macOS release gate failing closed on setup and transcript validation

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _existing_source("src/app/gui_perf/macos_smf_dynlib_release_gate.spl")
expect(source).to_contain("reason=transcript-dir-create-failed")
expect(source).to_contain("val saved_transcript = rt_file_read_text(transcript_path)")
expect(source).to_contain("reason=transcript-readback-mismatch")
expect(source).to_contain("gui_mac_smf_dynlib_transcript_check_row(saved_transcript)")
expect(source.contains("gui_mac_smf_dynlib_transcript_check_row(stdout)")).to_equal(false)
expect(source).to_contain("reason=transcript-check-failed")
expect(source).to_contain("check_row == \"GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass\"")
expect(source.contains("check_row.contains(\"status=pass\")")).to_equal(false)
expect(source).to_contain("GUI_MAC_SMF_DYNLIB_RELEASE_GATE status=pass")
```

</details>

#### keeps SMF artifact contract helpers free of WM, web renderer, and native GUI runtime deps

1.  expect release clean

2.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/app/gui_perf/smf_dynlib_artifact.spl")
_expect_release_clean("src/app/gui_perf/smf_artifact_contract.spl")
```

</details>

#### keeps QEMU ARM64 SMF parity evidence free of WM, web renderer, and native GUI runtime deps

1.  expect release clean

2.  expect release clean

3.  expect release clean

4.  expect release clean

5.  expect release clean

6.  expect release clean


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_parity.spl")
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_parity_evidence.spl")
_expect_release_clean("src/app/gui_perf/simpleos_smf_dynload.spl")
_expect_release_clean("src/app/gui_perf/simpleos_smf_dynload_evidence.spl")
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_loader_parity.spl")
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_loader_parity_evidence.spl")
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

#### keeps exported dynlib hot symbol delegated to the pure command boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _existing_source("src/app/gui_perf/pure_gui_hot_dynlib_export.spl")
expect(source).to_contain("gui_representative_hot_probe_event_tick(iteration, pointer_x, pointer_y, key_code)")
expect(_text_has(source, "_pure_gui_hot_command_count")).to_equal(false)
```

</details>

#### documents legacy Rust SMF helpers as outside GUI release evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guide = _existing_source("doc/07_guide/dynlib_api.md")
expect(guide).to_contain("Legacy runtime SMF file helpers are not the GUI release lane")
expect(guide).to_contain("not accepted GUI release-lane evidence")
expect(guide).to_contain("src/app/gui_perf/smf_dynlib_artifact.spl")
expect(guide).to_contain("src/app/gui_perf/simpleos_smf_dynload.spl")
expect(guide).to_contain("src/app/gui_perf/smf_dynlib_probe.spl")
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
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

