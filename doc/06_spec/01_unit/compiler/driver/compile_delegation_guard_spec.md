# Contract spec: test/01_unit/compiler/driver/compile_delegation_guard_spec.spl

> Audience: engineers owning the module under test. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/compile_delegation_guard_spec.spl

Audience: engineers owning the module under test. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/compile_delegation_guard_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the module under test. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/driver/compile_delegation_guard_spec.spl` and a green Results line.

## Scenarios

### compile delegation guard (fork-bomb regression)

#### resolves the Simple pid without a shell-parent hop

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves the Simple pid without a shell-parent hop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the Simple pid without a shell-parent hop")
val source = read_file("src/compiler/80.driver/driver_public_shared.spl")
expect(source).to_contain("\"/proc/{rt_getpid()}/exe\"")
expect(source).to_not_contain("/proc/$PPID/exe")
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

- Canonical SPipe generation for source `678cbb34c3307901b8614ffb72137954ac92a3ef79684e6268a85ca7d6523f0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `678cbb34c3307901b8614ffb72137954ac92a3ef79684e6268a85ca7d6523f0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `678cbb34c3307901b8614ffb72137954ac92a3ef79684e6268a85ca7d6523f0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/compile_delegation_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/compile_delegation_guard_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/compile_delegation_guard_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the Simple pid without a shell-parent hop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/compile_delegation_guard_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks when the delegation marker is already set by a parent in the chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/compile_delegation_guard_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks when the resolved external binary is this same running executable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
