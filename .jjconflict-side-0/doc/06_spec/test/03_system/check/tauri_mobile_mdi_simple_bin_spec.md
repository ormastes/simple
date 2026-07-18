# Tauri Mobile MDI Simple Binary Contract

> Tauri mobile MDI evidence is part of GUI renderer parity. The host-side wrapper must run source checks and screenshot validators through self-hosted Simple, not the Rust bootstrap seed, while preserving platform artifact checks for Android and iOS evidence.

<!-- sdn-diagram:id=tauri_mobile_mdi_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_mobile_mdi_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_mobile_mdi_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_mobile_mdi_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Mobile MDI Simple Binary Contract

Tauri mobile MDI evidence is part of GUI renderer parity. The host-side wrapper must run source checks and screenshot validators through self-hosted Simple, not the Rust bootstrap seed, while preserving platform artifact checks for Android and iOS evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/tauri_mobile_mdi_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tauri mobile MDI evidence is part of GUI renderer parity. The host-side wrapper
must run source checks and screenshot validators through self-hosted Simple, not
the Rust bootstrap seed, while preserving platform artifact checks for Android
and iOS evidence.

## Requirements

**Requirements:** N/A

- REQ-TAURI-MOBILE-MDI-BIN-001: Default host Simple binary selection is
  self-hosted only.
- REQ-TAURI-MOBILE-MDI-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before smoke, Android, or iOS helper work.
- REQ-TAURI-MOBILE-MDI-BIN-003: Evidence records selected Simple binary,
  source, and status fields.
- REQ-TAURI-MOBILE-MDI-BIN-004: iOS MDI helper self-tests receive the selected
  Simple binary and source provenance.

## Plan

**Plan:** doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Inspect iOS helper invocations for forwarded Simple binary provenance.
4. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
5. Confirm platform smoke/helper logs are not created on the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates the host `SIMPLE_BIN` before invoking source checks,
Android screenshot/log validators, or iOS helper self-tests.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_mobile_mdi_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### Tauri mobile MDI Simple binary contract

#### selects self hosted Simple and forwards launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-tauri-mobile-mdi-evidence.shs")
expect(script).to_contain("BUILD_DIR=")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("/release/*/simple")
expect(script).to_contain("/bin/release/*/simple")
expect(script).to_contain("/build/bootstrap/stage3/simple")
expect(script).to_contain("/bin/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("tauri_mobile_mdi_simple_bin=")
expect(script).to_contain("tauri_mobile_mdi_simple_bin_source=")
expect(script).to_contain("tauri_mobile_mdi_simple_bin_status=")
expect(script).to_contain("sh \"$IOS_MDI_EVIDENCE\" --self-test")
expect(script).to_contain("sh \"$IOS_MDI_EVIDENCE\" --browser-self-test")
expect(script).to_contain("sh \"$IOS_MDI_EVIDENCE\" --tauri-url-self-test")
```

</details>

#### rejects explicit Rust seed before mobile platform work

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-mobile-mdi-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out sh scripts/check/check-tauri-mobile-mdi-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("status=fail")
expect(output).to_contain("reason=simple-bin-forbidden")
expect(output).to_contain("tauri_mobile_mdi_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("tauri_mobile_mdi_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("tauri_mobile_mdi_simple_bin_status=forbidden")

val (_smoke_out, _smoke_err, smoke_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/mobile_mdi_smoke_check.log"])
expect(smoke_code).to_equal(0)
val (_ios_out, _ios_err, ios_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/ios_mdi_probe_self_test.log"])
expect(ios_code).to_equal(0)
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

- **Plan:** [doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md](doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md)
- **Design:** [doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md](doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md](doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md)


</details>
