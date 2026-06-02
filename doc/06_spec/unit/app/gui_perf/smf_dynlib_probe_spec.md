# Smf Dynlib Probe Specification

## Scenarios

### pure GUI SMF dynlib probe

#### builds a representative pure GUI workload without pixels

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = gui_dynlib_probe_workload(3)
expect(events.len()).to_equal(4)
expect(events[0].kind).to_equal("pointer_move")
expect(events[3].kind).to_equal("key")
```

</details>

#### fails closed for direct Simple fallback samples

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GuiDynlibProbeConfig(
    artifact_path: "build/gui/pure_gui.smf",
    symbol_name: "gui_dynlib_hot_probe_tick",
    iterations: 4,
    warmup_count: 1,
    threshold_us: 1000
)
val evidence = GuiDynlibProbeLoadEvidence(
    loader_mode: "smf_dynlib",
    call_source: "direct_simple",
    symbol_resolved: true,
    fallback_used: true,
    dynlib_path: ""
)
val report = gui_dynlib_probe_report(config, evidence, [10, 11, 12, 13])
expect(report.pass).to_equal(false)
expect(report.error).to_equal("not-dynlib-hot-call")
expect(report.call_source).to_equal("direct_simple")
```

</details>

#### fails closed for SMF registry symbols that are not process-callable

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GuiDynlibProbeConfig(
    artifact_path: "build/gui/pure_gui.smf",
    symbol_name: "gui_dynlib_hot_probe_tick",
    iterations: 4,
    warmup_count: 1,
    threshold_us: 1000
)
val evidence = GuiDynlibProbeLoadEvidence(
    loader_mode: "smf_dynlib",
    call_source: "registry_symbol_only",
    symbol_resolved: true,
    fallback_used: true,
    dynlib_path: ""
)
val report = gui_dynlib_probe_report(config, evidence, [10, 11, 12, 13])
expect(report.pass).to_equal(false)
expect(report.error).to_equal("not-dynlib-hot-call")
expect(report.call_source).to_equal("registry_symbol_only")
```

</details>

#### reports missing artifact as direct Simple fallback

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GuiDynlibProbeConfig(
    artifact_path: "",
    symbol_name: "gui_dynlib_hot_probe_tick",
    iterations: 4,
    warmup_count: 1,
    threshold_us: 1000
)
val evidence = GuiDynlibProbeLoadEvidence(
    loader_mode: "direct_simple",
    call_source: "direct_simple",
    symbol_resolved: false,
    fallback_used: true,
    dynlib_path: ""
)
val report = gui_dynlib_probe_report(config, evidence, [10])
expect(report.pass).to_equal(false)
expect(report.error).to_equal("missing-artifact-path")
```

</details>

#### recognizes host dynamic libraries as diagnostic artifacts only

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_dynlib_probe_is_host_dynlib_path("build/gui/libpure_gui_hot.so")).to_equal(true)
expect(gui_dynlib_probe_is_host_dynlib_path("build/gui/libpure_gui_hot.dylib")).to_equal(true)
expect(gui_dynlib_probe_is_host_dynlib_path("build/gui/pure_gui.smf")).to_equal(false)
```

</details>

#### recognizes SMF dynlib envelopes separately from host dynlibs

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_dynlib_probe_is_smf_dynlib_path("build/gui/pure_gui.smf")).to_equal(true)
expect(gui_dynlib_probe_is_smf_dynlib_path("build/gui/libpure_gui_hot.so")).to_equal(false)
```

</details>

#### uses host-specific cache names for extracted SMF libraries

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_dynlib_probe_host_dynlib_extension("macos")).to_equal(".dylib")
expect(gui_dynlib_probe_host_dynlib_extension("linux")).to_equal(".so")
expect(gui_dynlib_probe_smf_cache_path("build/gui/pure_gui.smf", "macos")).to_equal("build/gui/pure_gui.smf.extracted.dylib")
expect(gui_dynlib_probe_smf_cache_path("build/gui/pure_gui.smf", "linux")).to_equal("build/gui/pure_gui.smf.extracted.so")
```

</details>

#### extracts SMF dynlib bytes only for the matching host architecture

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 2u8, 1u8, 1u8, 0u8]
val arm64_smf = gui_smf_wrap_native_library(stub, 3u8)
expect(gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "arm64").len()).to_equal(stub.len())
expect(gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "aarch64").len()).to_equal(stub.len())
expect(gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "x86_64").len()).to_equal(0)
expect(gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "unknown").len()).to_equal(0)
```

</details>

#### compares extracted SMF cache bytes exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8, 3u8])).to_equal(true)
expect(gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8])).to_equal(false)
expect(gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8, 4u8])).to_equal(false)
```

</details>

#### verifies SMF cache writes by reading back the extracted dynlib bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_gui_smf_probe_cache_verify.bin"
val bytes = [0xCFu8, 0xFAu8, 0xEDu8, 0xFEu8, 1u8, 2u8]
expect(gui_dynlib_probe_write_cache_bytes_verified(path, bytes)).to_equal(true)
val reread = rt_file_read_bytes(path) ?? []
expect(gui_dynlib_probe_bytes_equal(bytes, reread)).to_equal(true)
expect(gui_dynlib_probe_write_cache_bytes_verified(path, [])).to_equal(false)
```

</details>

#### rejects callable host dynlib samples as not SMF dynlib acceptance

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GuiDynlibProbeConfig(
    artifact_path: "build/gui/libpure_gui_hot.so",
    symbol_name: "gui_dynlib_hot_probe_tick",
    iterations: 4,
    warmup_count: 1,
    threshold_us: 1000
)
val evidence = GuiDynlibProbeLoadEvidence(
    loader_mode: "host_dynlib",
    call_source: "dynlib_symbol_call",
    symbol_resolved: true,
    fallback_used: false,
    dynlib_path: "build/gui/libpure_gui_hot.so"
)
val report = gui_dynlib_probe_report(config, evidence, [10, 11, 12, 13])
expect(report.pass).to_equal(false)
expect(report.error).to_equal("not-smf-dynlib")
expect(report.call_source).to_equal("dynlib_symbol_call")
```

</details>

#### can report a real dynlib symbol hot-call sample set

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GuiDynlibProbeConfig(
    artifact_path: "build/gui/pure_gui.smf",
    symbol_name: "gui_dynlib_hot_probe_tick",
    iterations: 4,
    warmup_count: 1,
    threshold_us: 1000
)
val evidence = GuiDynlibProbeLoadEvidence(
    loader_mode: "smf_dynlib",
    call_source: "dynlib_symbol_call",
    symbol_resolved: true,
    fallback_used: false,
    dynlib_path: "build/gui/pure_gui.smf.extracted.so"
)
val report = gui_dynlib_probe_report(config, evidence, [10, 11, 12, 13])
expect(report.pass).to_equal(true)
expect(report.call_source).to_equal("dynlib_symbol_call")
```

</details>

#### records the settled dynlib path for a callable host artifact

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GuiDynlibProbeConfig(
    artifact_path: "build/gui/missing.so",
    symbol_name: "gui_dynlib_hot_probe_tick",
    iterations: 4,
    warmup_count: 1,
    threshold_us: 1000
)
val evidence = gui_dynlib_probe_load_host_evidence(config)
if evidence.call_source == "dynlib_symbol_call":
    expect(evidence.dynlib_path).to_equal(config.artifact_path)
else:
    expect(evidence.dynlib_path).to_equal("")
```

</details>

<details>
<summary>Advanced: reuses a stable event argument buffer in the measured hot loop</summary>

#### reuses a stable event argument buffer in the measured hot loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/gui_perf/smf_dynlib_probe_core.spl")
expect(source.contains("var args: [i64] = [0, 12, 24, 65]")).to_equal(true)
expect(source.contains("args[0] = i.to_i64()")).to_equal(true)
expect(source.contains("args[1] = 12 + i.to_i64()")).to_equal(true)
expect(source.contains("spl_wffi_call_i64(sym, args, 4)")).to_equal(true)
expect(source.contains("var args: [i64] = []")).to_equal(false)
expect(source.contains("args.push(i.to_i64())")).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/gui_perf/smf_dynlib_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pure GUI SMF dynlib probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

