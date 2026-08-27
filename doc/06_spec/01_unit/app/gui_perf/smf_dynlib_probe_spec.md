# Smf Dynlib Probe Specification

> Tests covering pure GUI SMF dynlib probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Dynlib Probe Specification

## Scenarios

### pure GUI SMF dynlib probe

#### builds a representative pure GUI workload without pixels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a representative pure GUI workload without pixels
   - Expected: events.len() equals `4`
   - Expected: events[0].kind equals `pointer_move`
   - Expected: events[3].kind equals `key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds a representative pure GUI workload without pixels")
val events = gui_dynlib_probe_workload(3)
expect(events.len()).to_equal(4)
expect(events[0].kind).to_equal("pointer_move")
expect(events[3].kind).to_equal("key")
```

</details>

#### fails closed for direct Simple fallback samples

- fails closed for direct Simple fallback samples
   - Expected: report.pass is false
   - Expected: report.error equals `not-dynlib-hot-call`
   - Expected: report.call_source equals `direct_simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for direct Simple fallback samples")
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

- fails closed for SMF registry symbols that are not process-callable
   - Expected: report.pass is false
   - Expected: report.error equals `not-dynlib-hot-call`
   - Expected: report.call_source equals `registry_symbol_only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for SMF registry symbols that are not process-callable")
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

- reports missing artifact as direct Simple fallback
   - Expected: report.pass is false
   - Expected: report.error equals `missing-artifact-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports missing artifact as direct Simple fallback")
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

- recognizes host dynamic libraries as diagnostic artifacts only
   - Expected: gui_dynlib_probe_is_host_dynlib_path("build/gui/libpure_gui_hot.so") is true
   - Expected: gui_dynlib_probe_is_host_dynlib_path("build/gui/libpure_gui_hot.dylib") is true
   - Expected: gui_dynlib_probe_is_host_dynlib_path("build/gui/pure_gui.smf") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recognizes host dynamic libraries as diagnostic artifacts only")
expect(gui_dynlib_probe_is_host_dynlib_path("build/gui/libpure_gui_hot.so")).to_equal(true)
expect(gui_dynlib_probe_is_host_dynlib_path("build/gui/libpure_gui_hot.dylib")).to_equal(true)
expect(gui_dynlib_probe_is_host_dynlib_path("build/gui/pure_gui.smf")).to_equal(false)
```

</details>

#### recognizes SMF dynlib envelopes separately from host dynlibs

- recognizes SMF dynlib envelopes separately from host dynlibs
   - Expected: gui_dynlib_probe_is_smf_dynlib_path("build/gui/pure_gui.smf") is true
   - Expected: gui_dynlib_probe_is_smf_dynlib_path("build/gui/libpure_gui_hot.so") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recognizes SMF dynlib envelopes separately from host dynlibs")
expect(gui_dynlib_probe_is_smf_dynlib_path("build/gui/pure_gui.smf")).to_equal(true)
expect(gui_dynlib_probe_is_smf_dynlib_path("build/gui/libpure_gui_hot.so")).to_equal(false)
```

</details>

#### uses host-specific cache names for extracted SMF libraries

- uses host-specific cache names for extracted SMF libraries
   - Expected: gui_dynlib_probe_host_dynlib_extension("macos") equals `.dylib`
   - Expected: gui_dynlib_probe_host_dynlib_extension("linux") equals `.so`
   - Expected: gui_dynlib_probe_smf_cache_path("build/gui/pure_gui.smf", "macos") equals `build/gui/pure_gui.smf.extracted.dylib`
   - Expected: gui_dynlib_probe_smf_cache_path("build/gui/pure_gui.smf", "linux") equals `build/gui/pure_gui.smf.extracted.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses host-specific cache names for extracted SMF libraries")
expect(gui_dynlib_probe_host_dynlib_extension("macos")).to_equal(".dylib")
expect(gui_dynlib_probe_host_dynlib_extension("linux")).to_equal(".so")
expect(gui_dynlib_probe_smf_cache_path("build/gui/pure_gui.smf", "macos")).to_equal("build/gui/pure_gui.smf.extracted.dylib")
expect(gui_dynlib_probe_smf_cache_path("build/gui/pure_gui.smf", "linux")).to_equal("build/gui/pure_gui.smf.extracted.so")
```

</details>

#### extracts SMF dynlib bytes only for the matching host architecture

- extracts SMF dynlib bytes only for the matching host architecture
   - Expected: gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "arm64").len() equals `stub.len()`
   - Expected: gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "aarch64").len() equals `stub.len()`
   - Expected: gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "x86_64").len() equals `0`
   - Expected: gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "unknown").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts SMF dynlib bytes only for the matching host architecture")
val stub = [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 2u8, 1u8, 1u8, 0u8]
val arm64_smf = gui_smf_wrap_native_library(stub, 3u8)
expect(gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "arm64").len()).to_equal(stub.len())
expect(gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "aarch64").len()).to_equal(stub.len())
expect(gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "x86_64").len()).to_equal(0)
expect(gui_dynlib_probe_extract_smf_library_bytes_for_host_arch(arm64_smf, "unknown").len()).to_equal(0)
```

</details>

#### compares extracted SMF cache bytes exactly

- compares extracted SMF cache bytes exactly
   - Expected: gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8, 3u8]) is true
   - Expected: gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8]) is false
   - Expected: gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8, 4u8]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("compares extracted SMF cache bytes exactly")
expect(gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8, 3u8])).to_equal(true)
expect(gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8])).to_equal(false)
expect(gui_dynlib_probe_bytes_equal([1u8, 2u8, 3u8], [1u8, 2u8, 4u8])).to_equal(false)
```

</details>

#### verifies SMF cache writes by reading back the extracted dynlib bytes

- verifies SMF cache writes by reading back the extracted dynlib bytes
   - Expected: gui_dynlib_probe_write_cache_bytes_verified(path, bytes) is true
   - Expected: gui_dynlib_probe_bytes_equal(bytes, reread) is true
   - Expected: gui_dynlib_probe_write_cache_bytes_verified(path, []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("verifies SMF cache writes by reading back the extracted dynlib bytes")
val path = "/tmp/simple_gui_smf_probe_cache_verify.bin"
val bytes = [0xCFu8, 0xFAu8, 0xEDu8, 0xFEu8, 1u8, 2u8]
expect(gui_dynlib_probe_write_cache_bytes_verified(path, bytes)).to_equal(true)
val reread = rt_file_read_bytes(path) ?? []
expect(gui_dynlib_probe_bytes_equal(bytes, reread)).to_equal(true)
expect(gui_dynlib_probe_write_cache_bytes_verified(path, [])).to_equal(false)
```

</details>

#### rejects callable host dynlib samples as not SMF dynlib acceptance

- rejects callable host dynlib samples as not SMF dynlib acceptance
   - Expected: report.pass is false
   - Expected: report.error equals `not-smf-dynlib`
   - Expected: report.call_source equals `dynlib_symbol_call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects callable host dynlib samples as not SMF dynlib acceptance")
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

- can report a real dynlib symbol hot-call sample set
   - Expected: report.pass is true
   - Expected: report.call_source equals `dynlib_symbol_call`
   - Expected: report.loader_mode equals `smf_dynlib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("can report a real dynlib symbol hot-call sample set")
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
expect(report.loader_mode).to_equal("smf_dynlib")
```

</details>

#### records the settled dynlib path for a callable host artifact

- records the settled dynlib path for a callable host artifact
   - Expected: evidence.dynlib_path equals `config.artifact_path`
   - Expected: evidence.dynlib_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("records the settled dynlib path for a callable host artifact")
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

- reuses a stable event argument buffer in the measured hot loop
   - Expected: source contains `var args: [i64] = [0, 12, 24, 65]`
   - Expected: source contains `args[0] = i.to_i64()`
   - Expected: source contains `args[1] = 12 + i.to_i64()`
   - Expected: source contains `spl_wffi_call_i64(sym, args, 4)`
   - Expected: source does not contain `var args: [i64] = []`
   - Expected: source does not contain `args.push(i.to_i64())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reuses a stable event argument buffer in the measured hot loop")
val source = rt_file_read_text("src/app/gui_perf/smf_dynlib_probe_core.spl")
expect(source).to_contain("use std.sffi.dynamic.{spl_dlopen, spl_dlsym, spl_dlclose, spl_wffi_call_i64}")
expect(source).to_contain("val handle = spl_dlopen(cache_path)")
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
| Source | `test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure GUI SMF dynlib probe.
- pure GUI SMF dynlib probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ece81466792c257ccd0ab83362da382f222b2ed87c9af4c947c6bea94e464d03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ece81466792c257ccd0ab83362da382f222b2ed87c9af4c947c6bea94e464d03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ece81466792c257ccd0ab83362da382f222b2ed87c9af4c947c6bea94e464d03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **69/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl
mirror: doc/06_spec/01_unit/app/gui_perf/smf_dynlib_probe_spec.md (current)
findings: 9 blockers: 2
  narrative=100 structure=95 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=69; blocker cap makes effective=49
doc/06_spec/01_unit/app/gui_perf/smf_dynlib_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/gui_perf/smf_dynlib_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a representative pure GUI workload without pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes host dynamic libraries as diagnostic artifacts only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes SMF dynlib envelopes separately from host dynlibs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl:175:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can report a real dynlib symbol hot-call sample set' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
