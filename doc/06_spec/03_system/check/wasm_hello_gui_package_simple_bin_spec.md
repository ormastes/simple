# WASM Hello GUI Package Simple Binary Contract

> This wrapper is part of GUI/WASM renderer hardening. It must not compile through `src/compiler_rust` or `cargo run`; the package evidence must exercise the selected Simple binary directly.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WASM Hello GUI Package Simple Binary Contract

This wrapper is part of GUI/WASM renderer hardening. It must not compile through `src/compiler_rust` or `cargo run`; the package evidence must exercise the selected Simple binary directly.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/mobile_wasm_gui/mobile_simple_wasm_gui_plan.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/wasm_hello_gui_package_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This wrapper is part of GUI/WASM renderer hardening. It must not compile through
`src/compiler_rust` or `cargo run`; the package evidence must exercise the
selected Simple binary directly.

## Requirements

**Requirements:** N/A

- REQ-WASM-HELLO-GUI-BIN-001: Default Simple binary selection is self-hosted
  only.
- REQ-WASM-HELLO-GUI-BIN-002: Explicit Rust seed paths fail closed with
  `simple-bin-forbidden` before source or compile work.
- REQ-WASM-HELLO-GUI-BIN-003: WASM compilation is performed by the selected
  Simple binary, not by `cargo run` under `src/compiler_rust`.
- REQ-WASM-HELLO-GUI-BIN-004: Evidence records Simple binary, source, and
  status fields.

## Plan

**Plan:** doc/03_plan/ui/mobile_wasm_gui/mobile_simple_wasm_gui_plan.md

1. Inspect the wrapper source for self-hosted binary candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Inspect the compile path to ensure it uses the selected Simple binary.
4. Run the wrapper with a Rust seed override.
5. Confirm the forbidden path exits before source or compile logs are created.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before executing the GUI source contract or
compiling the WASM artifact, keeping the failure path cheap and deterministic.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/wasm_hello_gui_package_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### WASM hello GUI package Simple binary contract

#### uses self hosted Simple for execution and compilation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses self hosted Simple for execution and compilation
   - Expected: cargo_code equals `1`
   - Expected: seed_dir_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses self hosted Simple for execution and compilation")
val script = file_read("scripts/check/check-wasm-hello-gui-package-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("run_with_timeout")
expect(script).to_contain(" compile ")
expect(script).to_contain("wasm_hello_gui_simple_bin=")
expect(script).to_contain("wasm_hello_gui_simple_bin_source=")
expect(script).to_contain("wasm_hello_gui_simple_bin_status=")
val (_cargo_out, _cargo_err, cargo_code) = process_run("/bin/sh", ["-c", "grep -F 'cargo run -q -p simple-driver' scripts/check/check-wasm-hello-gui-package-evidence.shs >/dev/null"])
expect(cargo_code).to_equal(1)
val (_seed_dir_out, _seed_dir_err, seed_dir_code) = process_run("/bin/sh", ["-c", "grep -E 'cd .*src/compiler_rust' scripts/check/check-wasm-hello-gui-package-evidence.shs >/dev/null"])
expect(seed_dir_code).to_equal(1)
```

</details>

#### rejects explicit Rust seed before source or compile execution

- rejects explicit Rust seed before source or compile execution
   - Expected: code equals `0`
   - Expected: source_code equals `0`
   - Expected: compile_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before source or compile execution")
val root = "build/test-wasm-hello-gui-package-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-wasm-hello-gui-package-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("wasm_hello_gui_package_status=fail")
expect(output).to_contain("wasm_hello_gui_package_reason=simple-bin-forbidden")
expect(output).to_contain("wasm_hello_gui_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("wasm_hello_gui_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("wasm_hello_gui_simple_bin_status=forbidden")

val (_source_out, _source_err, source_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/source.log"])
expect(source_code).to_equal(0)
val (_compile_out, _compile_err, compile_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/compile.log"])
expect(compile_code).to_equal(0)
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
- `REQ-WASM-HELLO-GUI-BIN-001:`
- `REQ-WASM-HELLO-GUI-BIN-002:`
- `REQ-WASM-HELLO-GUI-BIN-003:`
- `REQ-WASM-HELLO-GUI-BIN-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b31e8bb9061c4fa981e4bc3700c04bd52c73606df7eebe6da900646b0de93143`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b31e8bb9061c4fa981e4bc3700c04bd52c73606df7eebe6da900646b0de93143`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b31e8bb9061c4fa981e4bc3700c04bd52c73606df7eebe6da900646b0de93143`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/wasm_hello_gui_package_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/wasm_hello_gui_package_simple_bin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/wasm_hello_gui_package_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/wasm_hello_gui_package_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/wasm_hello_gui_package_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/wasm_hello_gui_package_simple_bin_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses self hosted Simple for execution and compilation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/wasm_hello_gui_package_simple_bin_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before source or compile execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
