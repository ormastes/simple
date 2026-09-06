# GUI WASM Host WM Launch Simple Binary Contract

> The host WM launch evidence depends on the target-package and CLI-artifact wrappers. This contract keeps the full chain on pure Simple/self-hosted binaries for GUI/WASM renderer evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI WASM Host WM Launch Simple Binary Contract

The host WM launch evidence depends on the target-package and CLI-artifact wrappers. This contract keeps the full chain on pure Simple/self-hosted binaries for GUI/WASM renderer evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/mobile_wasm_gui/mobile_simple_wasm_gui_plan.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The host WM launch evidence depends on the target-package and CLI-artifact
wrappers. This contract keeps the full chain on pure Simple/self-hosted
binaries for GUI/WASM renderer evidence.

## Requirements

**Requirements:** N/A

- REQ-GUI-WASM-HOST-WM-BIN-001: The host wrapper selects only self-hosted
  Simple binaries by default.
- REQ-GUI-WASM-HOST-WM-BIN-002: Rust seed overrides produce
  `simple-bin-forbidden` before child wrappers or WM bridge launch.
- REQ-GUI-WASM-HOST-WM-BIN-003: The host wrapper calls the target-package
  wrapper through the canonical `scripts/check/` path.
- REQ-GUI-WASM-HOST-WM-BIN-004: The target-package wrapper forwards the
  selected Simple binary and source provenance to the CLI-artifact wrapper.

## Plan

**Plan:** doc/03_plan/ui/mobile_wasm_gui/mobile_simple_wasm_gui_plan.md

1. Inspect host and child wrapper sources for self-hosted binary selection.
2. Inspect the target-package wrapper for the canonical child script path.
3. Run the host wrapper with a Rust seed `SIMPLE_BIN` override.
4. Confirm stdout and report show `simple-bin-forbidden`.
5. Confirm target-package and host bridge logs are not created for the
   forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The host wrapper validates `SIMPLE_BIN` before target package generation and
before the temporary host WM bridge is created.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### GUI WASM host WM launch Simple binary contract

#### selects self hosted Simple and forwards launcher provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and forwards launcher provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and forwards launcher provenance")
val host = file_read("scripts/check/check-gui-wasm-host-wm-launch-evidence.shs")
expect(host).to_contain("SIMPLE_BIN_SOURCE=")
expect(host).to_contain("SIMPLE_BIN_STATUS=pass")
expect(host).to_contain("\"release\"/*/simple")
expect(host).to_contain("\"bin/release\"/*/simple")
expect(host).to_contain("\"build/bootstrap/stage3/simple\"")
expect(host).to_contain("\"bin/simple\"")
expect(host).to_contain("is_rust_seed_simple")
expect(host).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(host).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(host).to_contain("scripts/check/check-gui-wasm-target-package-evidence.shs")
expect(host).to_contain("gui_wasm_host_wm_launch_simple_bin=")
expect(host).to_contain("gui_wasm_host_wm_launch_simple_bin_source=")
expect(host).to_contain("gui_wasm_host_wm_launch_simple_bin_status=")

val target = file_read("scripts/check/check-gui-wasm-target-package-evidence.shs")
expect(target).to_contain("scripts/check/check-gui-wasm-cli-artifact.shs")
expect(target).to_contain("SIMPLE_BIN=")
expect(target).to_contain("SIMPLE_BIN_SOURCE=")

val cli = file_read("scripts/check/check-gui-wasm-cli-artifact.shs")
expect(cli).to_contain("is_rust_seed_simple")
expect(cli).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(cli).to_contain("gui_wasm_cli_simple_bin=")
expect(cli).to_contain("gui_wasm_cli_simple_bin_source=")
expect(cli).to_contain("gui_wasm_cli_simple_bin_status=")
```

</details>

#### rejects explicit Rust seed before target package or WM bridge execution

- rejects explicit Rust seed before target package or WM bridge execution
   - Expected: code equals `0`
   - Expected: target_code equals `0`
   - Expected: server_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before target package or WM bridge execution")
val root = "build/test-gui-wasm-host-wm-launch-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md GUI_WASM_TARGET_PACKAGE_BUILD_DIR=" + root + "/target GUI_WASM_TARGET_PACKAGE_REPORT_PATH=" + root + "/target.md sh scripts/check/check-gui-wasm-host-wm-launch-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("gui_wasm_host_wm_launch_status=unavailable")
expect(output).to_contain("gui_wasm_host_wm_launch_reason=simple-bin-forbidden")
expect(output).to_contain("gui_wasm_host_wm_launch_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("gui_wasm_host_wm_launch_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("gui_wasm_host_wm_launch_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason: simple-bin-forbidden")
val (_target_out, _target_err, target_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/target-package.out"])
expect(target_code).to_equal(0)
val (_server_out, _server_err, server_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/host-wm-server.out"])
expect(server_code).to_equal(0)
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

- **Plan:** `doc/03_plan/ui/mobile_wasm_gui/mobile_simple_wasm_gui_plan.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-GUI-WASM-HOST-WM-BIN-001:`
- `REQ-GUI-WASM-HOST-WM-BIN-002:`
- `REQ-GUI-WASM-HOST-WM-BIN-003:`
- `REQ-GUI-WASM-HOST-WM-BIN-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2f5dcfbbe5a03c9b97192c6c9997be21e7a19227343588f860248af0eab9936d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f5dcfbbe5a03c9b97192c6c9997be21e7a19227343588f860248af0eab9936d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f5dcfbbe5a03c9b97192c6c9997be21e7a19227343588f860248af0eab9936d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and forwards launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_wasm_host_wm_launch_simple_bin_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before target package or WM bridge execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
