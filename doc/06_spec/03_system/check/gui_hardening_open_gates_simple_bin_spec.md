# GUI Hardening Open Gates Simple Binary Contract

> The open-gates wrapper can launch multiple GUI browser/corpus SSpecs. This contract keeps that launcher on repo self-hosted Simple binaries and makes Rust seed rejection deterministic and cheap.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Hardening Open Gates Simple Binary Contract

The open-gates wrapper can launch multiple GUI browser/corpus SSpecs. This contract keeps that launcher on repo self-hosted Simple binaries and makes Rust seed rejection deterministic and cheap.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The open-gates wrapper can launch multiple GUI browser/corpus SSpecs. This
contract keeps that launcher on repo self-hosted Simple binaries and makes Rust
seed rejection deterministic and cheap.

## Requirements

**Requirements:** N/A

- REQ-GUI-HARDENING-GATES-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-GUI-HARDENING-GATES-BIN-002: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence before any corpus specs run.
- REQ-GUI-HARDENING-GATES-BIN-003: Failure evidence records selected Simple
  binary, source, status, and report path.
- REQ-GUI-HARDENING-GATES-BIN-004: An executable that cannot interpret the
  bounded startup probe produces `simple-bin-startup-failed` before corpus
  specs run.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Confirm stdout reports `simple-bin-forbidden`.
5. Confirm no corpus spec summary is created for the forbidden path.
6. Run the wrapper with `/bin/false` and confirm startup admission fails.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates the launcher before artifact snapshots and before any
browser/corpus SSpec process is spawned.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### GUI hardening open gates Simple binary contract

#### selects self hosted Simple and records launcher provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and records launcher provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and records launcher provenance")
val script = file_read("scripts/check/check-gui-hardening-open-gates.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("simple_binary_startup_usable")
expect(script).to_contain("SIMPLE_BOOTSTRAP_DRIVER=\"$resolved\"")
expect(script).to_contain("SIMPLE_BOOTSTRAP_DRIVER=\"$SIMPLE_BIN_RESOLVED\"")
expect(script).to_contain("timeout -k 2 \"$SIMPLE_STARTUP_TIMEOUT_SECONDS\"")
expect(script).to_contain("timeout -k 5 \"$timeout_seconds\"")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("SIMPLE_BIN_STATUS=startup-failed")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_RESOLVED SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("gui_hardening_open_gates_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("gui_hardening_open_gates_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("gui_hardening_open_gates_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### rejects explicit Rust seed before running browser corpus specs

- rejects explicit Rust seed before running browser corpus specs
   - Expected: code equals `0`
   - Expected: ls_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before running browser corpus specs")
val root = "build/test-gui-hardening-open-gates-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gui-hardening-open-gates.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("gui_hardening_open_gates_status=fail")
expect(output).to_contain("gui_hardening_open_gates_reason=simple-bin-forbidden")
expect(output).to_contain("gui_hardening_open_gates_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("gui_hardening_open_gates_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("gui_hardening_open_gates_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason=simple-bin-forbidden")
val (_ls_out, _ls_err, ls_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/spec-summary.txt"])
expect(ls_code).to_equal(0)
```

</details>

#### rejects an executable that fails the bounded startup probe

- rejects an executable that fails the bounded startup probe
   - Expected: code equals `0`
   - Expected: ls_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an executable that fails the bounded startup probe")
val root = "build/test-gui-hardening-open-gates-startup-failed"
val command = "rm -rf " + root + " && SIMPLE_BIN=/bin/false BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gui-hardening-open-gates.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("gui_hardening_open_gates_status=fail")
expect(output).to_contain("gui_hardening_open_gates_reason=simple-bin-startup-failed")
expect(output).to_contain("gui_hardening_open_gates_simple_bin=/bin/false")
expect(output).to_contain("gui_hardening_open_gates_simple_bin_status=startup-failed")

val (_ls_out, _ls_err, ls_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/spec-summary.txt"])
expect(ls_code).to_equal(0)
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

- **Plan:** `doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-GUI-HARDENING-GATES-BIN-001:`
- `REQ-GUI-HARDENING-GATES-BIN-002:`
- `REQ-GUI-HARDENING-GATES-BIN-003:`
- `REQ-GUI-HARDENING-GATES-BIN-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3cb7754f5e61c6d8bae0d0e941142a15f8118b37fe41ffd0c3f2bf60211ac9c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3cb7754f5e61c6d8bae0d0e941142a15f8118b37fe41ffd0c3f2bf60211ac9c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3cb7754f5e61c6d8bae0d0e941142a15f8118b37fe41ffd0c3f2bf60211ac9c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/gui_hardening_open_gates_simple_bin_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_hardening_open_gates_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_hardening_open_gates_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and records launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before running browser corpus specs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an executable that fails the bounded startup probe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
