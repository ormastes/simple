# VHDL Backend Toolchain

> As a hardware-backend maintainer I need the GHDL/Yosys wrappers to answer "is the toolchain here?" truthfully on a host that has no toolchain at all, so that a machine without GHDL degrades to a clean negative instead of a crash or a false positive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Backend Toolchain

As a hardware-backend maintainer I need the GHDL/Yosys wrappers to answer "is the toolchain here?" truthfully on a host that has no toolchain at all, so that a machine without GHDL degrades to a clean negative instead of a crash or a false positive.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-002 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/usage/vhdl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

As a hardware-backend maintainer I need the GHDL/Yosys wrappers to answer
"is the toolchain here?" truthfully on a host that has no toolchain at all, so
that a machine without GHDL degrades to a clean negative instead of a crash or
a false positive.

What is assertable unconditionally is the `VhdlToolResult` record contract —
pure data, no toolchain. The `ghdl_available()` / `yosys_available()` probes are
NOT assertable here: they route through the extern `rt_process_run_capture`,
which is declared in `src/app/io/vhdl_sffi.spl` but implemented in neither the
Rust seed nor `src/runtime/`, so calling one aborts with
`semantic: unknown extern function: rt_process_run_capture`. They therefore stay
inside the `SIMPLE_VHDL_TEST=1` branch, where an operator who opened the gate
will see the real failure. Tracked in
`doc/08_tracking/bug/vhdl_sffi_rt_process_run_capture_extern_missing_2026-08-09.md`.

When the gate is closed this spec prints a VISIBLE skip and asserts nothing
about GHDL's behaviour.

## Syntax

```simple
if ghdl_available():
    val result = ghdl_analyze(path)
```

## Scenarios

### VHDL toolchain availability probes

#### carries exit code and both streams through VhdlToolResult

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries exit code and both streams through VhdlToolResult
- a tool result is a faithful record of what the tool reported
   - Expected: ok.exit_code equals `0`
   - Expected: ok.stdout equals `analysis complete`
   - Expected: ok.stderr equals ``
- a failure keeps its nonzero code and its diagnostic text
   - Expected: bad.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("carries exit code and both streams through VhdlToolResult")
step("a tool result is a faithful record of what the tool reported")
val ok = vhdl_tool_result(0, "analysis complete", "")
expect(ok.exit_code).to_equal(0)
expect(ok.stdout).to_equal("analysis complete")
expect(ok.stderr).to_equal("")

step("a failure keeps its nonzero code and its diagnostic text")
val bad = vhdl_tool_result(1, "", "syntax error near 'entty'")
expect(bad.exit_code).to_equal(1)
expect(bad.stderr).to_contain("syntax error")
```

</details>

### GHDL toolchain-backed analysis

#### invokes GHDL only when SIMPLE_VHDL_TEST is open, and skips visibly otherwise

- invokes GHDL only when SIMPLE_VHDL_TEST is open, and skips visibly otherwise
- gate CLOSED — no GHDL behaviour is asserted, and this is stated aloud
   - Expected: test_env_require("SIMPLE_VHDL_TEST") equals `blocked:SIMPLE_VHDL_TEST`
- gate OPEN — the operator asserts a toolchain is installed, so demand one
   - Expected: ghdl_available() is true
   - Expected: yosys_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("invokes GHDL only when SIMPLE_VHDL_TEST is open, and skips visibly otherwise")
if not test_env_vhdl_available():
    step("gate CLOSED — no GHDL behaviour is asserted, and this is stated aloud")
    print("SKIP (no GHDL assertion made): " + test_env_gate_reason("SIMPLE_VHDL_TEST"))
    expect(test_env_require("SIMPLE_VHDL_TEST")).to_equal("blocked:SIMPLE_VHDL_TEST")
else:
    step("gate OPEN — the operator asserts a toolchain is installed, so demand one")
    # NOTE: this currently aborts with `unknown extern function:
    # rt_process_run_capture` — that is the defect, surfaced rather
    # than hidden. See the bug record named in the docstring.
    expect(ghdl_available()).to_equal(true)
    expect(yosys_available()).to_equal(true)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f2b95c2fccc41c65bbcaea5b2c3ddb973d1dd82c395ed6bc8ab7da9a7b8d205`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f2b95c2fccc41c65bbcaea5b2c3ddb973d1dd82c395ed6bc8ab7da9a7b8d205`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f2b95c2fccc41c65bbcaea5b2c3ddb973d1dd82c395ed6bc8ab7da9a7b8d205`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/usage/vhdl_spec.spl
mirror: doc/06_spec/03_system/feature/usage/vhdl_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/vhdl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/vhdl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/vhdl_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/vhdl_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries exit code and both streams through VhdlToolResult' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/vhdl_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invokes GHDL only when SIMPLE_VHDL_TEST is open, and skips visibly otherwise' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
