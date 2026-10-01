# Pure Gui Release Lane Specification

> Tests covering pure GUI release lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Gui Release Lane Specification

## Scenarios

### pure GUI release lane

#### rejects hosted BrowserWindow and content web sources

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects hosted BrowserWindow and content web sources
   - Expected: _has_forbidden_release_dependency(_existing_source("src/lib/gui/entity/browser_window.spl")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects hosted BrowserWindow and content web sources")
expect(_has_forbidden_release_dependency(_existing_source("src/lib/gui/entity/browser_window.spl"))).to_equal(true)
```

</details>

#### rejects Skia-backed hosted presentation sources

- rejects Skia-backed hosted presentation sources
   - Expected: _has_forbidden_release_dependency(_existing_source("src/lib/gui/entity/printing.spl")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects Skia-backed hosted presentation sources")
expect(_has_forbidden_release_dependency(_existing_source("src/lib/gui/entity/printing.spl"))).to_equal(true)
```

</details>

#### keeps pure GUI release entry surface free of WM, web renderer, Skia, and native GUI runtime deps

- keeps pure GUI release entry surface free of WM, web renderer, Skia, and native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps pure GUI release entry surface free of WM, web renderer, Skia, and native GUI runtime deps")
_expect_release_clean("src/lib/gui/pure_release.spl")
```

</details>

#### keeps pure GUI command boundary free of WM, web renderer, and native GUI runtime deps

- keeps pure GUI command boundary free of WM, web renderer, and native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps pure GUI command boundary free of WM, web renderer, and native GUI runtime deps")
_expect_release_clean("src/lib/gui/pure_core.spl")
```

</details>

#### keeps pure GUI SMF dynlib perf contract free of WM, web renderer, and native GUI runtime deps

- keeps pure GUI SMF dynlib perf contract free of WM, web renderer, and native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps pure GUI SMF dynlib perf contract free of WM, web renderer, and native GUI runtime deps")
_expect_release_clean("src/lib/gui/pure_smf_dynlib_perf.spl")
```

</details>

#### keeps GUI SMF dynlib probe free of WM, web renderer, and native GUI runtime deps

- keeps GUI SMF dynlib probe free of WM, web renderer, and native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps GUI SMF dynlib probe free of WM, web renderer, and native GUI runtime deps")
_expect_release_clean("src/app/gui_perf/smf_dynlib_probe_core.spl")
_expect_release_clean("src/app/gui_perf/smf_dynlib_probe.spl")
```

</details>

#### rejects legacy Rust SMF and dyncall runtime helpers in GUI release sources

- rejects legacy Rust SMF and dyncall runtime helpers in GUI release sources
   - Expected: _has_forbidden_release_dependency("extern fn rt_file_wrap_smf_dynlib(input: text, output: text, arch: text) -> bool") is true
   - Expected: _has_forbidden_release_dependency("extern fn rt_file_extract_smf_dynlib(input: text, output: text) -> bool") is true
   - Expected: _has_forbidden_release_dependency("extern fn rt_dyncall_0(ptr: i64) -> i64") is true
   - Expected: _has_forbidden_release_dependency("extern fn rt_dyncall_1(ptr: i64, arg0: i64) -> i64") is true
   - Expected: _has_forbidden_release_dependency("extern fn rt_dyncall_6(ptr: i64, a: i64, b: i64, c: i64, d: i64, e: i64, f: i64) -> i64") is true
   - Expected: _has_forbidden_release_dependency("extern fn rt_webgpu_present(surface: i64) -> i64") is true
   - Expected: _has_forbidden_release_dependency("use std.sffi.dynamic.{spl_dlopen, spl_dlsym, spl_dlclose, spl_wffi_call_i64}") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects legacy Rust SMF and dyncall runtime helpers in GUI release sources")
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

- keeps macOS SMF evidence runner free of WM, web renderer, and native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps macOS SMF evidence runner free of WM, web renderer, and native GUI runtime deps")
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_evidence_core.spl")
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_evidence.spl")
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_transcript_check.spl")
_expect_release_clean("src/app/gui_perf/macos_smf_dynlib_release_gate.spl")
_expect_release_clean("src/app/gui_perf/linux_smf_dynlib_e2e_gate.spl")
```

</details>

#### keeps macOS release gate failing closed on setup and transcript validation

- keeps macOS release gate failing closed on setup and transcript validation
   - Expected: source does not contain `gui_mac_smf_dynlib_transcript_check_row(stdout)`
   - Expected: source does not contain `"check_row`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps macOS release gate failing closed on setup and transcript validation")
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

- keeps SMF artifact contract helpers free of WM, web renderer, and native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps SMF artifact contract helpers free of WM, web renderer, and native GUI runtime deps")
_expect_release_clean("src/app/gui_perf/smf_dynlib_artifact.spl")
_expect_release_clean("src/app/gui_perf/smf_artifact_contract.spl")
```

</details>

#### keeps QEMU ARM64 SMF parity evidence free of WM, web renderer, and native GUI runtime deps

- keeps QEMU ARM64 SMF parity evidence free of WM, web renderer, and native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps QEMU ARM64 SMF parity evidence free of WM, web renderer, and native GUI runtime deps")
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_parity.spl")
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_parity_evidence.spl")
_expect_release_clean("src/app/gui_perf/simpleos_smf_dynload.spl")
_expect_release_clean("src/app/gui_perf/simpleos_smf_dynload_evidence.spl")
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_loader_parity.spl")
_expect_release_clean("src/app/gui_perf/qemu_arm64_smf_loader_parity_evidence.spl")
```

</details>

#### keeps SMF wrapper and exported hot symbol free of WM, web renderer, and native GUI runtime deps

- keeps SMF wrapper and exported hot symbol free of WM, web renderer, and native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps SMF wrapper and exported hot symbol free of WM, web renderer, and native GUI runtime deps")
_expect_release_clean("src/app/gui_perf/smf_wrap_host_dynlib.spl")
_expect_release_clean("src/app/gui_perf/pure_gui_hot_dynlib_export.spl")
```

</details>

#### keeps exported dynlib hot symbol delegated to the pure command boundary

- keeps exported dynlib hot symbol delegated to the pure command boundary
   - Expected: _text_has(source, "_pure_gui_hot_command_count") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps exported dynlib hot symbol delegated to the pure command boundary")
val source = _existing_source("src/app/gui_perf/pure_gui_hot_dynlib_export.spl")
expect(source).to_contain("gui_representative_hot_probe_event_tick(iteration, pointer_x, pointer_y, key_code)")
expect(_text_has(source, "_pure_gui_hot_command_count")).to_equal(false)
```

</details>

#### documents legacy Rust SMF helpers as outside GUI release evidence

- documents legacy Rust SMF helpers as outside GUI release evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("documents legacy Rust SMF helpers as outside GUI release evidence")
val guide = _existing_source("doc/07_guide/dynlib_api.md")
expect(guide).to_contain("Legacy runtime SMF file helpers are not the GUI release lane")
expect(guide).to_contain("not accepted GUI release-lane evidence")
expect(guide).to_contain("src/app/gui_perf/smf_dynlib_artifact.spl")
expect(guide).to_contain("src/app/gui_perf/simpleos_smf_dynload.spl")
expect(guide).to_contain("src/app/gui_perf/smf_dynlib_probe.spl")
```

</details>

#### keeps BrowserWindow entity free of native GUI runtime deps

- keeps BrowserWindow entity free of native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps BrowserWindow entity free of native GUI runtime deps")
_expect_no_native_gui_runtime("src/lib/gui/entity/browser_window.spl")
```

</details>

#### keeps Menu entity free of native GUI runtime deps

- keeps Menu entity free of native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps Menu entity free of native GUI runtime deps")
_expect_no_native_gui_runtime("src/lib/gui/entity/menu.spl")
```

</details>

#### keeps IME entity free of native GUI runtime deps

- keeps IME entity free of native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps IME entity free of native GUI runtime deps")
_expect_no_native_gui_runtime("src/lib/gui/entity/ime.spl")
```

</details>

#### keeps Printing entity free of native GUI runtime deps

- keeps Printing entity free of native GUI runtime deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps Printing entity free of native GUI runtime deps")
_expect_no_native_gui_runtime("src/lib/gui/entity/printing.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gui/pure_gui_release_lane_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure GUI release lane.
- pure GUI release lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0b84c52971a001708470e8b4e2da39aad70ff464d72195e13f37b9e37dc32b7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b84c52971a001708470e8b4e2da39aad70ff464d72195e13f37b9e37dc32b7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b84c52971a001708470e8b4e2da39aad70ff464d72195e13f37b9e37dc32b7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gui/pure_gui_release_lane_spec.spl
mirror: doc/06_spec/01_unit/lib/gui/pure_gui_release_lane_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gui/pure_gui_release_lane_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gui/pure_gui_release_lane_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gui/pure_gui_release_lane_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gui/pure_gui_release_lane_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects hosted BrowserWindow and content web sources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gui/pure_gui_release_lane_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects Skia-backed hosted presentation sources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gui/pure_gui_release_lane_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps pure GUI release entry surface free of WM, web renderer, Skia, and native GUI runtime deps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
