# Linux Smf Dynlib E2e Gate Specification

## Scenarios

### Linux SMF dynlib e2e gate

#### builds the pure SMF dynlib command chain

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = gui_linux_smf_dynlib_e2e_default_paths("src/compiler_rust/target/debug/simple")
expect(paths.dynlib_path).to_equal("build/gui/libpure_gui_hot.so")
expect(paths.smf_path).to_equal("build/gui/pure_gui_hot.smf")
expect(gui_linux_smf_dynlib_e2e_compile_dynlib_command(paths)).to_contain("pure_gui_hot_dynlib_export.spl --native --shared --strip")
expect(gui_linux_smf_dynlib_e2e_compile_wrapper_command(paths)).to_contain("smf_wrap_host_dynlib.spl --native --strip")
expect(gui_linux_smf_dynlib_e2e_compile_probe_command(paths)).to_contain("smf_dynlib_probe.spl --native --strip")
expect(gui_linux_smf_dynlib_e2e_wrap_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARCH='x86_64'")
expect(gui_linux_smf_dynlib_e2e_wrap_command(paths)).to_contain("SIMPLE_GUI_SMF_OUTPUT='build/gui/pure_gui_hot.smf'")
expect(gui_linux_smf_dynlib_e2e_probe_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_ARTIFACT='build/gui/pure_gui_hot.smf'")
expect(gui_linux_smf_dynlib_e2e_probe_command(paths)).to_contain("SIMPLE_GUI_DYNLIB_HOST_PROFILE='linux-x86_64'")
```

</details>

#### accepts only Linux SFFI SMF dynlib hot probe rows

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val good = "GUI_DYNLIB_PERF artifact=build/gui/pure_gui_hot.smf dynlib_path=build/gui/pure_gui_hot.smf.extracted.so host_os=linux host_arch=x86_64 host_profile=linux-x86_64 host_cpu=linux-x86_64 loader=smf_dynlib dynload=smf_dynlib host_dynload=sffi symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 expected_samples=128 warmup=16 p50_us=1 p95_us=1 p99_us=1 max_us=1 threshold_us=1000 pass=true error="
val measured = "GUI_DYNLIB_PERF artifact=build/gui/pure_gui_hot.smf dynlib_path=build/gui/pure_gui_hot.smf.extracted.so host_os=linux host_arch=x86_64 host_profile=linux-x86_64 host_cpu=linux-x86_64 loader=smf_dynlib dynload=smf_dynlib host_dynload=sffi symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 expected_samples=128 warmup=16 p50_us=25 p95_us=32 p99_us=253 max_us=459 threshold_us=1000 pass=true error="
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good)).to_equal(true)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(measured)).to_equal(true)
expect(gui_linux_smf_dynlib_e2e_probe_reject_reason(measured)).to_equal("")
expect(gui_linux_smf_dynlib_e2e_probe_reject_reason("")).to_equal("missing-or-duplicate-probe-row")
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("artifact=build/gui/pure_gui_hot.smf", "artifact=build/gui/other.smf"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("dynlib_path=build/gui/pure_gui_hot.smf.extracted.so", "dynlib_path=build/gui/libpure_gui_hot.so"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("host_os=linux", "host_os=macos"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("loader=smf_dynlib", "loader=host_dynlib"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("dynload=smf_dynlib", "dynload=native"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("host_dynload=sffi", "host_dynload=native"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("call_source=dynlib_symbol_call", "call_source=direct_simple"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("samples=128", "samples=64"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("expected_samples=128", "expected_samples=64"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("threshold_us=1000", "threshold_us=5000"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("p99_us=1", "p99_us=1000"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good.replace("p99_us=1", "p99_us=abc"))).to_equal(false)
expect(gui_linux_smf_dynlib_e2e_probe_reject_reason(good.replace("p99_us=1", "p99_us=abc"))).to_equal("bad-p99-token")
expect(gui_linux_smf_dynlib_e2e_accepts_probe_row(good + " p99_us=1")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/gui_perf/linux_smf_dynlib_e2e_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Linux SMF dynlib e2e gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
