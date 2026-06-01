# Macos Smf Dynlib Evidence Specification

## Scenarios

### macOS SMF dynlib evidence helpers

#### accepts only macOS arm64 hosts

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_mac_smf_dynlib_is_arm64("arm64")).to_equal(true)
expect(gui_mac_smf_dynlib_is_arm64("aarch64")).to_equal(true)
expect(gui_mac_smf_dynlib_host_supported("macos", "arm64")).to_equal(true)
expect(gui_mac_smf_dynlib_host_supported("linux", "arm64")).to_equal(false)
expect(gui_mac_smf_dynlib_host_supported("macos", "x86_64")).to_equal(false)
```

</details>

#### uses stable macOS dylib and SMF artifact paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = gui_mac_smf_dynlib_default_paths("bin/simple")
expect(paths.dynlib_path).to_equal("build/gui/libpure_gui_hot.dylib")
expect(paths.smf_path).to_equal("build/gui/pure_gui_hot.smf")
expect(paths.wrapper_path).to_equal("build/gui/smf_wrap_host_dynlib")
expect(paths.probe_path).to_equal("build/gui/smf_dynlib_probe")
```

</details>

<details>
<summary>Advanced: builds shell commands for cold orchestration outside the hot loop</summary>

#### builds shell commands for cold orchestration outside the hot loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = gui_mac_smf_dynlib_default_paths("bin/simple")
expect(gui_mac_smf_dynlib_shell_quote("a'b")).to_equal("'a'\\''b'")
expect(gui_mac_smf_dynlib_compile_dynlib_command(paths)).to_contain("--shared")
expect(gui_mac_smf_dynlib_compile_dynlib_command(paths)).to_contain("libpure_gui_hot.dylib")
expect(gui_mac_smf_dynlib_wrap_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARCH='arm64'")
expect(gui_mac_smf_dynlib_wrap_command(paths)).to_contain("SIMPLE_GUI_SMF_OUTPUT='build/gui/pure_gui_hot.smf'")
expect(gui_mac_smf_dynlib_contract_command(paths)).to_contain("run src/app/gui_perf/smf_artifact_contract.spl")
expect(gui_mac_smf_dynlib_contract_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARTIFACT='build/gui/pure_gui_hot.smf'")
expect(gui_mac_smf_dynlib_probe_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARTIFACT='build/gui/pure_gui_hot.smf'")
```

</details>


</details>

#### accepts only role-2 arm64 SMF artifact contract rows

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val good = "GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf sha256=abc size=4096 smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64"
val missing = good.replace("status=pass", "status=missing")
val wrong_role = good.replace("smf_role=2", "smf_role=1")
val wrong_arch = good.replace("arch=3", "arch=1")
val no_dynlib = good.replace("embedded_dynlib=true", "embedded_dynlib=false")
val wrong_symbol = good.replace("symbol=gui_dynlib_hot_probe_tick", "symbol=other")
expect(gui_mac_smf_dynlib_accepts_contract_row(good)).to_equal(true)
expect(gui_mac_smf_dynlib_accepts_contract_row(missing)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(wrong_role)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(wrong_arch)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(no_dynlib)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_contract_row(wrong_symbol)).to_equal(false)
```

</details>

#### accepts only real SMF dynlib hot-call probe rows

<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val good = "GUI_DYNLIB_PERF artifact=build/gui/pure_gui_hot.smf dynlib_path=build/gui/pure_gui_hot.smf.extracted.dylib host_os=macos host_arch=arm64 loader=smf_dynlib symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 warmup=16 p50_us=1 p95_us=1 p99_us=1 max_us=1 threshold_us=1000 pass=true error="
val host = good.replace("loader=smf_dynlib", "loader=host_dynlib")
val direct = good.replace("call_source=dynlib_symbol_call", "call_source=direct_simple")
val fail = good.replace("pass=true error=", "pass=false error=not-smf-dynlib")
val wrong_cache = good.replace("dynlib_path=build/gui/pure_gui_hot.smf.extracted.dylib", "dynlib_path=")
val wrong_host = good.replace("host_os=macos", "host_os=linux")
val wrong_arch = good.replace("host_arch=arm64", "host_arch=x86_64")
val missing_p99 = good.replace("p99_us=1 ", "")
val loose_threshold = good.replace("threshold_us=1000", "threshold_us=5000")
val over_threshold = good.replace("p99_us=1", "p99_us=1000")
val inconsistent_pass = good.replace("p99_us=1", "p99_us=2500")
expect(gui_mac_smf_dynlib_row_value(good, "loader")).to_equal("smf_dynlib")
expect(gui_mac_smf_dynlib_row_i64(good, "p99_us")).to_equal(1i64)
expect(gui_mac_smf_dynlib_accepts_probe_row(good)).to_equal(true)
expect(gui_mac_smf_dynlib_accepts_probe_row(host)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(direct)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(fail)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_cache)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_host)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(wrong_arch)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(missing_p99)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(loose_threshold)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(over_threshold)).to_equal(false)
expect(gui_mac_smf_dynlib_accepts_probe_row(inconsistent_pass)).to_equal(false)
```

</details>

#### reports non-mac hosts as explicit skips

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = gui_mac_smf_dynlib_skip_row("linux", "x86_64")
expect(row).to_contain("status=skip")
expect(row).to_contain("requires-macos-arm64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- macOS SMF dynlib evidence helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

