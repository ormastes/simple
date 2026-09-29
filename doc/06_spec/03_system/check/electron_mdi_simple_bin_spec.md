# Electron MDI Simple Binary Contract

> Electron MDI evidence is part of GUI/web renderer hardening. The wrapper is called by aggregate WM capture evidence and can also run standalone, so it must not fall back to `src/compiler_rust/**` when no parent wrapper forwards a Simple binary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron MDI Simple Binary Contract

Electron MDI evidence is part of GUI/web renderer hardening. The wrapper is called by aggregate WM capture evidence and can also run standalone, so it must not fall back to `src/compiler_rust/**` when no parent wrapper forwards a Simple binary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/electron_mdi_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Electron MDI evidence is part of GUI/web renderer hardening. The wrapper is
called by aggregate WM capture evidence and can also run standalone, so it must
not fall back to `src/compiler_rust/**` when no parent wrapper forwards a
Simple binary.

## Requirements

**Requirements:** N/A

- REQ-ELECTRON-MDI-BIN-001: Default Simple binary selection is self-hosted
  only.
- REQ-ELECTRON-MDI-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before Electron, node, npm, xvfb, or validator work.
- REQ-ELECTRON-MDI-BIN-003: Evidence records selected Simple binary, source,
  and status fields.
- REQ-ELECTRON-MDI-BIN-004: Tests can isolate output through a `BUILD_DIR`
  override.

## Plan

**Plan:** doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
4. Confirm stdout shows `simple-bin-forbidden`.
5. Confirm Electron proof artifacts are not created for the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before checking host GUI dependencies or
launching Electron, keeping forbidden seed rejection deterministic.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_mdi_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### Electron MDI Simple binary contract

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
val script = file_read("scripts/check/check-electron-mdi-evidence.shs")
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
expect(script).to_contain("electron_mdi_simple_bin=")
expect(script).to_contain("electron_mdi_simple_bin_source=")
expect(script).to_contain("electron_mdi_simple_bin_status=")
```

</details>

#### rejects explicit Rust seed before Electron proof execution

- rejects explicit Rust seed before Electron proof execution
   - Expected: code equals `0`
   - Expected: proof_code equals `0`
   - Expected: shot_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before Electron proof execution")
val root = "build/test-electron-mdi-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out sh scripts/check/check-electron-mdi-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("status=fail")
expect(output).to_contain("reason=simple-bin-forbidden")
expect(output).to_contain("electron_mdi_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("electron_mdi_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("electron_mdi_simple_bin_status=forbidden")

val (_proof_out, _proof_err, proof_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/electron_mdi_proof.json"])
expect(proof_code).to_equal(0)
val (_shot_out, _shot_err, shot_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/electron_mdi.png"])
expect(shot_code).to_equal(0)
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
- `REQ-ELECTRON-MDI-BIN-001:`
- `REQ-ELECTRON-MDI-BIN-002:`
- `REQ-ELECTRON-MDI-BIN-003:`
- `REQ-ELECTRON-MDI-BIN-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `75b0b825edd39a3f8c4288ca2c2dff57547b5a0861cf26c655476453c9ba6db4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75b0b825edd39a3f8c4288ca2c2dff57547b5a0861cf26c655476453c9ba6db4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75b0b825edd39a3f8c4288ca2c2dff57547b5a0861cf26c655476453c9ba6db4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/electron_mdi_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/electron_mdi_simple_bin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/electron_mdi_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/electron_mdi_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/electron_mdi_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/electron_mdi_simple_bin_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and records launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/electron_mdi_simple_bin_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before Electron proof execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
