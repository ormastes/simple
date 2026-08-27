# Compile Delegation Guard Specification

> Tests covering compile delegation guard (fork-bomb regression).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Delegation Guard Specification

## Scenarios

### compile delegation guard (fork-bomb regression)

#### resolves the Simple pid without a shell-parent hop

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves the Simple pid without a shell-parent hop
   - Expected: source does not contain `/proc/$PPID/exe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the Simple pid without a shell-parent hop")
val source = read_file("src/compiler/80.driver/driver_public_shared.spl")
expect(source).to_contain("\"/proc/{rt_getpid()}/exe\"")
expect(source.contains("/proc/$PPID/exe")).to_equal(false)
```

</details>

#### blocks when the delegation marker is already set by a parent in the chain

- blocks when the delegation marker is already set by a parent in the chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("blocks when the delegation marker is already set by a parent in the chain")
val result = compile_delegation_guard_decision(
    "backend=vhdl", "1", "bin/release/simple",
    "/opt/simple/bin/release/x86_64-unknown-linux-gnu/simple"
)
check(result != "")
check(result.contains("compile delegation loop detected"))
check(result.contains("backend=vhdl"))
```

</details>

#### blocks when the resolved external binary is this same running executable

- blocks when the resolved external binary is this same running executable


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("blocks when the resolved external binary is this same running executable")
val result = compile_delegation_guard_decision(
    "native", "",
    "/opt/simple/bin/release/x86_64-unknown-linux-gnu/simple",
    "/opt/simple/bin/release/x86_64-unknown-linux-gnu/simple"
)
check(result != "")
check(result.contains("native"))
```

</details>

#### allows a legitimate delegation to a distinct external binary with no marker set

- allows a legitimate delegation to a distinct external binary with no marker set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows a legitimate delegation to a distinct external binary with no marker set")
val result = compile_delegation_guard_decision(
    "backend=c", "",
    "src/compiler_rust/target/bootstrap/simple",
    "/opt/simple/bin/release/x86_64-unknown-linux-gnu/simple"
)
expect result == ""
```

</details>

#### treats a relative resolved path ending in the current exe's basename as the same binary

- treats a relative resolved path ending in the current exe's basename as the same binary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a relative resolved path ending in the current exe's basename as the same binary")
check(is_same_binary_path("bin/simple", "/opt/simple/bin/simple"))
check(is_same_binary_path("/opt/simple/bin/simple", "bin/simple"))
check(not is_same_binary_path("bin/simple", "/opt/simple/bin/other_simple"))
check(not is_same_binary_path("", "/opt/simple/bin/simple"))
```

</details>

#### builds a clear, actionable error message

- builds a clear, actionable error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds a clear, actionable error message")
val msg = compile_delegation_guard_message("backend=vhdl")
expect msg == "compile delegation loop detected: external fallback resolves to this same CLI; backend=vhdl not supported in-process"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/compile_delegation_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compile delegation guard (fork-bomb regression).
- compile delegation guard (fork-bomb regression)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35df104fcd3b8f8731b80c343344895aa2d31529601f4b2ad73369a7c8850cd8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35df104fcd3b8f8731b80c343344895aa2d31529601f4b2ad73369a7c8850cd8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35df104fcd3b8f8731b80c343344895aa2d31529601f4b2ad73369a7c8850cd8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/compile_delegation_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/compile_delegation_guard_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/compile_delegation_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/compile_delegation_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/compile_delegation_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/driver/compile_delegation_guard_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the Simple pid without a shell-parent hop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/compile_delegation_guard_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks when the delegation marker is already set by a parent in the chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/compile_delegation_guard_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks when the resolved external binary is this same running executable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
