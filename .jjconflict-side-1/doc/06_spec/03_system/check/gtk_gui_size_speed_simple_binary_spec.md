# GTK GUI Size/Speed Simple Binary Contract

> The GTK size/speed baseline is part of GUI performance evidence. It must not silently use `src/compiler_rust/**` when collecting Simple renderer timings or native-size artifacts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GTK GUI Size/Speed Simple Binary Contract

The GTK size/speed baseline is part of GUI performance evidence. It must not silently use `src/compiler_rust/**` when collecting Simple renderer timings or native-size artifacts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The GTK size/speed baseline is part of GUI performance evidence. It must not
silently use `src/compiler_rust/**` when collecting Simple renderer timings or
native-size artifacts.

## Requirements

**Requirements:** N/A

- REQ-GTK-GUI-PERF-BIN-001: Default Simple binary selection is self-hosted only.
- REQ-GTK-GUI-PERF-BIN-002: Rust seed Simple paths produce
  `simple-binary-forbidden` evidence before render/native/GTK probes run.
- REQ-GTK-GUI-PERF-BIN-003: Evidence records selected Simple binary, source,
  and status fields.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BINARY=src/compiler_rust/target/release/simple`.
4. Confirm stdout and report record `simple-binary-forbidden`.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BINARY` before running Simple rendering, native
builds, or GTK C probes so forbidden seed rejection is cheap and deterministic.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl --mode=interpreter --clean
```

## Scenarios

### GTK GUI size/speed Simple binary contract

#### selects self hosted Simple and records launcher provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and records launcher provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and records launcher provenance")
val script = file_read("scripts/check/check-gtk-gui-size-speed-baseline.shs")
expect(script).to_contain("SIMPLE_BINARY_SOURCE=")
expect(script).to_contain("SIMPLE_BINARY_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple_binary")
expect(script).to_contain("SIMPLE_BINARY_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BINARY SIMPLE_BINARY_SOURCE SIMPLE_BINARY_STATUS")
expect(script).to_contain("simple_binary=$SIMPLE_BINARY")
expect(script).to_contain("simple_binary_source=$SIMPLE_BINARY_SOURCE")
expect(script).to_contain("simple_binary_status=$SIMPLE_BINARY_STATUS")
```

</details>

#### rejects explicit Rust seed before running GUI perf probes

- rejects explicit Rust seed before running GUI perf probes
   - Expected: code equals `0`
   - Expected: no_probe_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before running GUI perf probes")
val root = "build/test-gtk-gui-size-speed-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BINARY=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gtk-gui-size-speed-baseline.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("gtk_benchmark_evidence_status=unavailable")
expect(output).to_contain("gtk_benchmark_evidence_reason=simple-binary-forbidden")
expect(output).to_contain("simple_binary=src/compiler_rust/target/release/simple")
expect(output).to_contain("simple_binary_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("simple_binary_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("| reason | simple-binary-forbidden |")
val (_test_out, _test_err, no_probe_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/simple_gui_render_bench.trial_1.out"])
expect(no_probe_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-GTK-GUI-PERF-BIN-001:`
- `REQ-GTK-GUI-PERF-BIN-002:`
- `REQ-GTK-GUI-PERF-BIN-003:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60a43e1faf9fadc1d30e12f0f794f3b109d4a0fffc6671a3ae134c03736a299f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60a43e1faf9fadc1d30e12f0f794f3b109d4a0fffc6671a3ae134c03736a299f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60a43e1faf9fadc1d30e12f0f794f3b109d4a0fffc6671a3ae134c03736a299f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl
mirror: doc/06_spec/03_system/check/gtk_gui_size_speed_simple_binary_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gtk_gui_size_speed_simple_binary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gtk_gui_size_speed_simple_binary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and records launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before running GUI perf probes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
