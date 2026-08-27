# Vhdl Backend Cli Smoke Specification

> Tests covering VHDL backend CLI smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Backend Cli Smoke Specification

## Scenarios

### VHDL backend CLI smoke

#### bin/simple compile --backend=vhdl writes the requested .vhd output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bin/simple compile --backend=vhdl writes the requested .vhd output
   - Expected: code equals `0`
   - Expected: rt_file_exists(out_path) is true
   - Expected: output.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple compile --backend=vhdl writes the requested .vhd output")
val src_path = "/tmp/simple_vhdl_cli_explicit.spl"
val out_path = "/tmp/simple_vhdl_cli_explicit.vhd"
delete_if_exists(src_path)
delete_if_exists(out_path)
write_source(src_path, "add")

val (_stdout, _stderr, code) = rt_process_run("bin/simple", ["compile", "--backend=vhdl", src_path, "-o", out_path])

expect(code).to_equal(0)
expect(rt_file_exists(out_path)).to_equal(true)
val output = rt_file_read_text(out_path)
expect(output.len() > 0).to_equal(true)
expect(output).to_contain("entity add is")
expect(output).to_contain("tmp_4 <= a + b;")
expect(output).to_contain("result_out <= tmp_4;")

delete_if_exists(src_path)
delete_if_exists(out_path)
```

</details>

#### bin/simple compile --backend=vhdl writes the default .vhd output

- bin/simple compile --backend=vhdl writes the default .vhd output
   - Expected: code equals `0`
   - Expected: rt_file_exists(out_path) is true
   - Expected: output.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple compile --backend=vhdl writes the default .vhd output")
val src_path = "/tmp/simple_vhdl_cli_default.spl"
val out_path = "/tmp/simple_vhdl_cli_default.vhd"
delete_if_exists(src_path)
delete_if_exists(out_path)
write_source(src_path, "merge")

val (_stdout, _stderr, code) = rt_process_run("bin/simple", ["compile", "--backend=vhdl", src_path])

expect(code).to_equal(0)
expect(rt_file_exists(out_path)).to_equal(true)
val output = rt_file_read_text(out_path)
expect(output.len() > 0).to_equal(true)
expect(output).to_contain("entity merge is")
expect(output).to_contain("tmp_4 <= a + b;")
expect(output).to_contain("result_out <= tmp_4;")

delete_if_exists(src_path)
delete_if_exists(out_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/vhdl_backend_cli_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL backend CLI smoke.
- VHDL backend CLI smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `29ed355ac3bf47f1bb6b5387fa1de3172d5ba3758d79686a42f9a798b1a1e3b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29ed355ac3bf47f1bb6b5387fa1de3172d5ba3758d79686a42f9a798b1a1e3b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29ed355ac3bf47f1bb6b5387fa1de3172d5ba3758d79686a42f9a798b1a1e3b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/compiler/vhdl_backend_cli_smoke_spec.spl
mirror: doc/06_spec/03_system/compiler/vhdl_backend_cli_smoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/vhdl_backend_cli_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/vhdl_backend_cli_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/vhdl_backend_cli_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/vhdl_backend_cli_smoke_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bin/simple compile --backend=vhdl writes the requested .vhd output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/vhdl_backend_cli_smoke_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bin/simple compile --backend=vhdl writes the default .vhd output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
