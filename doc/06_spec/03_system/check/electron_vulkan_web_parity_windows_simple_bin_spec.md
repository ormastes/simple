# Electron Vulkan Web Parity Windows Simple Binary Contract

> The Windows wrapper is platform-specific, but its binary-selection contract can be checked on any host because the forbidden-seed path exits before Node, Electron, or Vulkan are required.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron Vulkan Web Parity Windows Simple Binary Contract

The Windows wrapper is platform-specific, but its binary-selection contract can be checked on any host because the forbidden-seed path exits before Node, Electron, or Vulkan are required.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/graphics/backends/graphical_backend_equality.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/electron_vulkan_web_parity_windows_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The Windows wrapper is platform-specific, but its binary-selection contract can
be checked on any host because the forbidden-seed path exits before Node,
Electron, or Vulkan are required.

## Requirements

**Requirements:** N/A

- REQ-EVWP-WIN-BIN-001: Default Simple binary selection is self-hosted only.
- REQ-EVWP-WIN-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before Electron startup.
- REQ-EVWP-WIN-BIN-003: Evidence stdout records selected Simple binary,
  source, and status fields.
- REQ-EVWP-WIN-BIN-004: Windows execution probes `SIMPLE_BIN --version` and
  rejects executables that do not identify as Simple.

## Plan

**Plan:** doc/03_plan/ui/graphics/backends/graphical_backend_equality.md

1. Inspect the Windows wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
4. Confirm stdout shows `simple-bin-forbidden`.
5. Confirm Electron capture artifacts are not created.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before launching Electron or the Simple web
renderer, so invalid Rust seed overrides cannot masquerade as Windows Vulkan
evidence.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_vulkan_web_parity_windows_simple_bin_spec.spl --mode=interpreter --clean
```

## Evidence Fields

The wrapper must emit binary provenance before any Windows GUI work can be
trusted:

- `electron_vulkan_web_parity_windows_simple_bin`
- `electron_vulkan_web_parity_windows_simple_bin_source`
- `electron_vulkan_web_parity_windows_simple_bin_status`
- `electron_vulkan_web_parity_windows_simple_bin_probe_exit_code`
- `electron_vulkan_web_parity_windows_simple_bin_version`
- `electron_vulkan_web_parity_windows_status`
- `electron_vulkan_web_parity_windows_reason`

The status field is `pass` only for an accepted self-hosted runtime. It is
`forbidden` when an explicit path points into `src/compiler_rust`, because that
would make the evidence a bootstrap/seed run instead of a pure-Simple-backed
Windows Vulkan GUI run.

## Completion Boundary

This spec does not launch Electron or prove a Windows Vulkan driver. It locks
the prerequisite launcher contract that must hold before the Windows parity
wrapper may be trusted. A later Windows run can only count as evidence if this
binary selection layer rejects seed paths and records the selected self-hosted
binary.

## Failure Semantics

- `simple-bin-forbidden`: explicit `SIMPLE_BIN` is a Rust seed path and must
  fail before browser capture starts.
- `simple-bin-missing`: Windows host did not provide or discover a self-hosted
  Simple executable.
- `simple-bin-probe-failed`: selected executable could not answer
  `--version`.
- `simple-bin-version-not-simple`: selected executable ran, but its version row
  did not identify it as Simple.
- `self-hosted:<path>`: the wrapper selected a repo-local self-hosted candidate.
- `explicit-env-rust-seed-forbidden`: the caller overrode `SIMPLE_BIN` with a
  forbidden seed path.

## Test Matrix

The spec contains:

- Static source inspection for self-hosted Windows `.exe` candidates,
  `bin/simple` fallback, seed detection, and structured emission fields.
- A real wrapper invocation with `SIMPLE_BIN=src/compiler_rust/...` that proves
  the forbidden path exits before any Electron capture file can be created.

## Windows Operator Checklist

1. Prefer the release self-hosted `simple.exe` produced by bootstrap.
2. Set `SIMPLE_BIN` only when selecting a known self-hosted executable.
3. Never set `SIMPLE_BIN` to `src/compiler_rust/...`.
4. Preserve stdout from the wrapper as the provenance record.
5. Treat a missing provenance row as invalid Windows GUI/Vulkan evidence.
6. Continue to the parity wrapper only after this contract is satisfied.

## Scenarios

### Electron Vulkan web parity Windows Simple binary contract

#### selects self hosted Simple and records launcher provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and records launcher provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and records launcher provenance")
val script = file_read("scripts/check/check-electron-vulkan-web-parity-windows.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"$ROOT\"/bin/release/*/simple.exe")
expect(script).to_contain("\"$ROOT\"/release/*/simple.exe")
expect(script).to_contain("\"$ROOT\"/build/bootstrap/stage3/simple.exe")
expect(script).to_contain("\"$ROOT\"/bin/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("emit \"electron_vulkan_web_parity_windows_simple_bin\"")
expect(script).to_contain("emit \"electron_vulkan_web_parity_windows_simple_bin_source\"")
expect(script).to_contain("emit \"electron_vulkan_web_parity_windows_simple_bin_status\"")
expect(script).to_contain("electron_vulkan_web_parity_windows_simple_bin_probe_exit_code")
expect(script).to_contain("electron_vulkan_web_parity_windows_simple_bin_version")
expect(script).to_contain("simple-bin-probe-failed")
expect(script).to_contain("simple-bin-version-not-simple")
expect(script).to_contain("Simple Language")
```

</details>

#### rejects explicit Rust seed before Electron startup

- rejects explicit Rust seed before Electron startup
   - Expected: code equals `0`
   - Expected: capture_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before Electron startup")
val root = "build/test-electron-vulkan-web-parity-windows-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple WORK=" + root + "/work EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(output).to_contain("electron_vulkan_web_parity_windows_reason=simple-bin-forbidden")
expect(output).to_contain("electron_vulkan_web_parity_windows_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("electron_vulkan_web_parity_windows_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("electron_vulkan_web_parity_windows_simple_bin_status=forbidden")

val (_capture_out, _capture_err, capture_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/work/electron.json"])
expect(capture_code).to_equal(0)
```

</details>

#### rejects non Simple executable before Electron startup

- rejects non Simple executable before Electron startup
   - Expected: code equals `0`
   - Expected: capture_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects non Simple executable before Electron startup")
val root = "build/test-electron-vulkan-web-parity-windows-non-simple-bin"
val command = "rm -rf " + root + " && mkdir -p " + root + " && printf '%s\\n' '#!/bin/sh' 'echo not-simple-runtime' 'exit 0' > " + root + "/fake-simple && chmod +x " + root + "/fake-simple && OS=Windows_NT SIMPLE_BIN=$PWD/" + root + "/fake-simple EVWP_WORK=" + root + "/work sh scripts/check/check-electron-vulkan-web-parity-windows.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("electron_vulkan_web_parity_windows_status=fail")
expect(output).to_contain("electron_vulkan_web_parity_windows_reason=simple-bin-version-not-simple")
expect(output).to_contain("electron_vulkan_web_parity_windows_simple_bin_probe_exit_code=0")
expect(output).to_contain("electron_vulkan_web_parity_windows_simple_bin_version=not-simple-runtime")

val (_capture_out, _capture_err, capture_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/work/electron.json"])
expect(capture_code).to_equal(0)
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

- **Plan:** `doc/03_plan/ui/graphics/backends/graphical_backend_equality.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-EVWP-WIN-BIN-001:`
- `REQ-EVWP-WIN-BIN-002:`
- `REQ-EVWP-WIN-BIN-003:`
- `REQ-EVWP-WIN-BIN-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `57066da68806991c77d365077950a4927e8fbe13b2621cc30faac85d06bba4f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57066da68806991c77d365077950a4927e8fbe13b2621cc30faac85d06bba4f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57066da68806991c77d365077950a4927e8fbe13b2621cc30faac85d06bba4f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/check/electron_vulkan_web_parity_windows_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/electron_vulkan_web_parity_windows_simple_bin_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/electron_vulkan_web_parity_windows_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/electron_vulkan_web_parity_windows_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/electron_vulkan_web_parity_windows_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/electron_vulkan_web_parity_windows_simple_bin_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and records launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
