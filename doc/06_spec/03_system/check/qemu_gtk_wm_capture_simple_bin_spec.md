# QEMU GTK WM Capture Simple Binary Contract

> The QEMU GTK WM capture wrapper aggregates live QEMU capture, host GTK scene baseline, fake-QMP capture, and WM launch capture evidence. It must not default to the Rust bootstrap seed for host-side Simple execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU GTK WM Capture Simple Binary Contract

The QEMU GTK WM capture wrapper aggregates live QEMU capture, host GTK scene baseline, fake-QMP capture, and WM launch capture evidence. It must not default to the Rust bootstrap seed for host-side Simple execution.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/qemu_gtk_wm_capture_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The QEMU GTK WM capture wrapper aggregates live QEMU capture, host GTK scene
baseline, fake-QMP capture, and WM launch capture evidence. It must not default
to the Rust bootstrap seed for host-side Simple execution.

## Requirements

**Requirements:** N/A

- REQ-QEMU-GTK-WM-BIN-001: Default Simple binary selection is self-hosted only.
- REQ-QEMU-GTK-WM-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before QEMU, fake-QMP, WM, or GTK child evidence.
- REQ-QEMU-GTK-WM-BIN-003: Evidence records selected Simple binary, source,
  and status fields.
- REQ-QEMU-GTK-WM-BIN-004: The fake-QMP child wrapper uses the canonical
  `scripts/check/` path and receives the selected Simple provenance.

## Plan

**Plan:** doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Inspect fake-QMP and WM child wrapper invocations.
4. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
5. Confirm child evidence logs are not created on the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` immediately after creating its isolated
build/report directories and before QEMU display probing or child evidence
execution.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/qemu_gtk_wm_capture_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### QEMU GTK WM capture Simple binary contract

#### selects self hosted Simple and forwards launcher provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and forwards launcher provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and forwards launcher provenance")
val script = file_read("scripts/check/check-qemu-gtk-wm-capture-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("qemu_gtk_wm_capture_simple_bin=")
expect(script).to_contain("qemu_gtk_wm_capture_simple_bin_source=")
expect(script).to_contain("qemu_gtk_wm_capture_simple_bin_status=")
expect(script).to_contain("scripts/check/check-qemu-capture-fake-qmp-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
```

</details>

#### rejects explicit Rust seed before child evidence execution

- rejects explicit Rust seed before child evidence execution
   - Expected: code equals `0`
   - Expected: fake_code equals `0`
   - Expected: wm_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before child evidence execution")
val root = "build/test-qemu-gtk-wm-capture-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-qemu-gtk-wm-capture-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("qemu_gtk_wm_capture_status=fail")
expect(output).to_contain("qemu_gtk_wm_capture_reason=simple-bin-forbidden")
expect(output).to_contain("qemu_gtk_wm_capture_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("qemu_gtk_wm_capture_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("qemu_gtk_wm_capture_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason: simple-bin-forbidden")
val (_fake_out, _fake_err, fake_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/fake-qmp.out"])
expect(fake_code).to_equal(0)
val (_wm_out, _wm_err, wm_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/wm-host.out"])
expect(wm_code).to_equal(0)
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

- **Plan:** `doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-QEMU-GTK-WM-BIN-001:`
- `REQ-QEMU-GTK-WM-BIN-002:`
- `REQ-QEMU-GTK-WM-BIN-003:`
- `REQ-QEMU-GTK-WM-BIN-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da3e919deb81ce77e2ce6560c880b030d1af55a3a411d177211a72b6a2761ee6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da3e919deb81ce77e2ce6560c880b030d1af55a3a411d177211a72b6a2761ee6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da3e919deb81ce77e2ce6560c880b030d1af55a3a411d177211a72b6a2761ee6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/check/qemu_gtk_wm_capture_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/qemu_gtk_wm_capture_simple_bin_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/qemu_gtk_wm_capture_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/qemu_gtk_wm_capture_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/qemu_gtk_wm_capture_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
