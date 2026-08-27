# Tauri iOS Mobile MDI Simple Binary Contract

> The iOS MDI helper is called from the broader Tauri mobile MDI wrapper and can also run standalone. Its host-side Simple execution must use the self-hosted binary so GUI/mobile renderer evidence does not depend on the Rust bootstrap seed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri iOS Mobile MDI Simple Binary Contract

The iOS MDI helper is called from the broader Tauri mobile MDI wrapper and can also run standalone. Its host-side Simple execution must use the self-hosted binary so GUI/mobile renderer evidence does not depend on the Rust bootstrap seed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The iOS MDI helper is called from the broader Tauri mobile MDI wrapper and can
also run standalone. Its host-side Simple execution must use the self-hosted
binary so GUI/mobile renderer evidence does not depend on the Rust bootstrap
seed.

## Requirements

**Requirements:** N/A

- REQ-TAURI-IOS-MDI-BIN-001: Default host Simple binary selection is
  self-hosted only.
- REQ-TAURI-IOS-MDI-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before self-test, browser self-test, Tauri URL-mode,
  or simulator work.
- REQ-TAURI-IOS-MDI-BIN-003: Evidence records selected Simple binary, source,
  and status fields.
- REQ-TAURI-IOS-MDI-BIN-004: Tests can isolate output through a `BUILD_DIR`
  override.

## Plan

**Plan:** doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md

1. Inspect the helper source for self-hosted candidate selection.
2. Inspect the helper source for Rust seed detection and provenance fields.
3. Run the helper with a Rust seed `SIMPLE_BIN` override.
4. Confirm stdout shows `simple-bin-forbidden`.
5. Confirm self-test/browser/Tauri URL artifacts are not created.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The helper validates the host `SIMPLE_BIN` before any mode-specific work, so
the forbidden seed path remains deterministic and dependency-free.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### Tauri iOS mobile MDI Simple binary contract

#### selects self hosted Simple and records launcher provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and records launcher provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and records launcher provenance")
val script = file_read("scripts/check/check-tauri-ios-mobile-mdi-evidence.shs")
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
expect(script).to_contain("tauri_ios_mobile_mdi_simple_bin=")
expect(script).to_contain("tauri_ios_mobile_mdi_simple_bin_source=")
expect(script).to_contain("tauri_ios_mobile_mdi_simple_bin_status=")
```

</details>

#### preserves live MDI DOM and accepts compact-log raw openWindow markers

- preserves live MDI DOM and accepts compact-log raw openWindow markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves live MDI DOM and accepts compact-log raw openWindow markers")
val script = file_read("scripts/check/check-tauri-ios-mobile-mdi-evidence.shs")
expect(script).to_contain("has_open_window_marker()")
expect(script).to_contain("grep -q \"openWindow id=$window_id\"")
expect(script).to_contain("grep -q \"\\\"type\\\":\\\"openWindow\\\",\\\"windowId\\\":\\\"$window_id\\\"\"")
expect(script).to_contain("has_open_window_marker terminal")
expect(script).to_contain("has_open_window_marker files")
expect(script).to_contain("has_open_window_marker tasks")
expect(script).to_contain("has_open_window_marker settings")

val shell_source = file_read("tools/tauri-shell/src-tauri/src/lib.rs")
expect(shell_source).to_contain("delayed inline shell eval skipped reason=mdi-opened")
expect(shell_source).to_contain("MDI_OPEN_WINDOW_COUNT.load(Ordering::SeqCst) > 0")
expect(shell_source).to_contain("eprintln!(\"[tauri-shell] render, html_len={}\", html.len());")
expect(shell_source).to_contain("return;")
```

</details>

#### rejects explicit Rust seed before self-test or simulator work

- rejects explicit Rust seed before self-test or simulator work
   - Expected: code equals `0`
   - Expected: server_code equals `0`
   - Expected: browser_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before self-test or simulator work")
val root = "build/test-tauri-ios-mobile-mdi-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out sh scripts/check/check-tauri-ios-mobile-mdi-evidence.shs --self-test > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("status=fail")
expect(output).to_contain("reason=simple-bin-forbidden")
expect(output).to_contain("tauri_ios_mobile_mdi_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("tauri_ios_mobile_mdi_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("tauri_ios_mobile_mdi_simple_bin_status=forbidden")

val (_server_out, _server_err, server_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/ios_mdi_probe_server.log"])
expect(server_code).to_equal(0)
val (_browser_out, _browser_err, browser_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/ios_mdi_probe_browser.log"])
expect(browser_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/platform/mobile_tauri_gui_parallel_2026-05-29.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TAURI-IOS-MDI-BIN-001:`
- `REQ-TAURI-IOS-MDI-BIN-002:`
- `REQ-TAURI-IOS-MDI-BIN-003:`
- `REQ-TAURI-IOS-MDI-BIN-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `98e93914e03ac283bad51f75e2d72f6a05b64a37d508c17efa1372df11946d7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98e93914e03ac283bad51f75e2d72f6a05b64a37d508c17efa1372df11946d7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98e93914e03ac283bad51f75e2d72f6a05b64a37d508c17efa1372df11946d7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and records launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves live MDI DOM and accepts compact-log raw openWindow markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/tauri_ios_mobile_mdi_simple_bin_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before self-test or simulator work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
