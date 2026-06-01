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
    call_source: "direct_simple",
    symbol_resolved: true,
    fallback_used: true
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
    call_source: "registry_symbol_only",
    symbol_resolved: true,
    fallback_used: true
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

Runnable source: 16 lines folded for reproduction.
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
    fallback_used: true
)
val report = gui_dynlib_probe_report(config, evidence, [10])
expect(report.pass).to_equal(false)
expect(report.error).to_equal("missing-artifact-path")
```

</details>

#### can report a real dynlib symbol hot-call sample set

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
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
    fallback_used: false
)
val report = gui_dynlib_probe_report(config, evidence, [10, 11, 12, 13])
expect(report.pass).to_equal(true)
expect(report.call_source).to_equal("dynlib_symbol_call")
```

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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

