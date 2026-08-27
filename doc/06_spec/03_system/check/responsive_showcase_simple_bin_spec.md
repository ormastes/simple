# Responsive Showcase Simple Binary Contract

> The responsive showcase evidence proves three viewport/navigation layouts and optionally the macOS Metal lane. This contract keeps those showcase artifacts from being accepted when they are produced through `src/compiler_rust/**`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Responsive Showcase Simple Binary Contract

The responsive showcase evidence proves three viewport/navigation layouts and optionally the macOS Metal lane. This contract keeps those showcase artifacts from being accepted when they are produced through `src/compiler_rust/**`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/responsive_showcase_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The responsive showcase evidence proves three viewport/navigation layouts and
optionally the macOS Metal lane. This contract keeps those showcase artifacts
from being accepted when they are produced through `src/compiler_rust/**`.

## Requirements

**Requirements:** N/A

- REQ-RESPONSIVE-SHOWCASE-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-RESPONSIVE-SHOWCASE-BIN-002: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence before CPU or Metal lanes run.
- REQ-RESPONSIVE-SHOWCASE-BIN-003: Evidence records selected Simple binary,
  source, and status fields.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Confirm `status.env` reports `simple-bin-forbidden`.
5. Confirm no CPU or Metal lane log is created for the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before any responsive showcase lane runs, so
forbidden seed rejection is cheap and deterministic.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/responsive_showcase_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### Responsive showcase Simple binary contract

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
val script = file_read("scripts/check/check-responsive-showcase-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("responsive_showcase_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("responsive_showcase_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("responsive_showcase_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### rejects explicit Rust seed before running showcase lanes

- rejects explicit Rust seed before running showcase lanes
   - Expected: code equals `0`
   - Expected: cpu_code equals `0`
   - Expected: metal_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before running showcase lanes")
val root = "build/test-responsive-showcase-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out sh scripts/check/check-responsive-showcase-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/status.env")
expect(evidence).to_contain("responsive_showcase_status=fail")
expect(evidence).to_contain("responsive_showcase_reason=simple-bin-forbidden")
expect(evidence).to_contain("responsive_showcase_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("responsive_showcase_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("responsive_showcase_simple_bin_status=forbidden")

val (_cpu_out, _cpu_err, cpu_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/cpu.log"])
expect(cpu_code).to_equal(0)
val (_metal_out, _metal_err, metal_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/metal.log"])
expect(metal_code).to_equal(0)
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
- `REQ-RESPONSIVE-SHOWCASE-BIN-001:`
- `REQ-RESPONSIVE-SHOWCASE-BIN-002:`
- `REQ-RESPONSIVE-SHOWCASE-BIN-003:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c11c61e6b2cbb787cc89d07f625abc7054e174ad965e5385a0be9699978625d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c11c61e6b2cbb787cc89d07f625abc7054e174ad965e5385a0be9699978625d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c11c61e6b2cbb787cc89d07f625abc7054e174ad965e5385a0be9699978625d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/responsive_showcase_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/responsive_showcase_simple_bin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/responsive_showcase_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/responsive_showcase_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/responsive_showcase_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/responsive_showcase_simple_bin_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and records launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/responsive_showcase_simple_bin_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before running showcase lanes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
