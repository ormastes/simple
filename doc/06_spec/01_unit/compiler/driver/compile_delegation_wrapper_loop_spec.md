# Contract spec: test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl

> Audience: engineers owning the module under test. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl

Audience: engineers owning the module under test. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl` |
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
`bin/simple test test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl` and a green Results line.

## Scenarios

### release-wrapper self-delegation (delegation-loop regression)

#### blocks spawning the bin/release/simple wrapper from a deployed release runtime with no marker set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocks spawning the bin/release/simple wrapper from a deployed release runtime with no marker set


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("blocks spawning the bin/release/simple wrapper from a deployed release runtime with no marker set")
# The exact reproducing shape: no SIMPLE_COMPILE_DELEGATED marker,
# resolved binary is the wrapper, current exe is the deployed runtime
# the wrapper would exec. Pre-fix this returned "" and the facade
# spawned an unbounded re-entry chain.
val result = compile_delegation_guard_decision(
    "type check", "", "bin/release/simple",
    "/opt/simple/bin/release/x86_64-unknown-linux-gnu/simple"
)
check(result != "")
check(result.contains("compile delegation loop detected"))
```

</details>

#### blocks the wrapper by absolute path and from bootstrap-stage binaries too

- blocks the wrapper by absolute path and from bootstrap-stage binaries too


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("blocks the wrapper by absolute path and from bootstrap-stage binaries too")
check(is_release_wrapper_self_delegation(
    "/opt/simple/bin/release/simple",
    "/opt/simple/bin/release/x86_64-unknown-linux-gnu/simple"))
check(is_release_wrapper_self_delegation(
    "bin/release/simple",
    "/opt/simple/bootstrap/stage3/simple"))
```

</details>

#### still allows genuinely external binaries and unknown identities

- still allows genuinely external binaries and unknown identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still allows genuinely external binaries and unknown identities")
check(not is_release_wrapper_self_delegation(
    "src/compiler_rust/target/bootstrap/simple",
    "/opt/simple/bin/release/x86_64-unknown-linux-gnu/simple"))
check(not is_release_wrapper_self_delegation(
    "bin/release/simple", "/usr/local/bin/other_tool"))
check(not is_release_wrapper_self_delegation("bin/release/simple", ""))
check(not is_release_wrapper_self_delegation("", "/opt/simple/bin/release/x86_64-unknown-linux-gnu/simple"))
```

</details>

### delegation-cycle generalization: every external spawn in the driver facades is guarded

#### guards every rt_process_run(simple_bin, ...) call site with the delegation guard

- guards every rt_process_run(simple_bin, ...) call site with the delegation guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guards every rt_process_run(simple_bin, ...) call site with the delegation guard")
# Probes for SIMILAR cycles: any facade function that spawns the
# resolved `simple` binary must consult check_compile_delegation_guard
# first. A new unguarded spawn is a fresh loop waiting to happen.
val facades = [
    "src/compiler/80.driver/driver_public_compile_process.spl",
    "src/compiler/80.driver/driver_public_compile_backends.spl",
    "src/compiler/80.driver/driver_public_shared.spl"
]
for facade in facades:
    val source = read_file(facade)
    if source.contains("rt_process_run(simple_bin"):
        check(source.contains("check_compile_delegation_guard("))
        check(source.contains("mark_compile_delegated()"))
```

</details>

#### keeps the lightweight facade lightweight: it never loads the full in-process driver

- keeps the lightweight facade lightweight: it never loads the full in-process driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the lightweight facade lightweight: it never loads the full in-process driver")
# The delegating facade must stay a pure process-spawner. Importing the
# full driver here would make every selective import evaluate the whole
# compiler graph under the test interpreter.
val source = read_file("src/compiler/80.driver/driver_public_compile_process.spl")
expect(source).to_not_contain("use lazy compiler.driver.driver_api_compile_single")        expect(source).to_not_contain("compiler_driver_create")
```

</details>

#### fires the wrapper rule inside the full decision core, not only the helper

- fires the wrapper rule inside the full decision core, not only the helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires the wrapper rule inside the full decision core, not only the helper")
val result = compile_delegation_guard_decision(
    "aot compile", "", "/repo/bin/release/simple",
    "/repo/bin/release/aarch64-unknown-linux-gnu/simple"
)
check(result != "")
```

</details>

### delegation-cycle root cause: the external facade must not shadow the in-process driver

#### defines every delegating entry point under a distinct external_ name

- defines every delegating entry point under a distinct external_ name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("defines every delegating entry point under a distinct external_ name")
val delegator = read_file("src/compiler/80.driver/driver_public_compile_process.spl")
val in_process = read_file("src/compiler/80.driver/driver_api_compile_single.spl")
for name in COLLIDING:
    # The in-process driver keeps the short name...
    check(in_process.contains("pub fn " + name + "("))
    # ...and the delegator must NOT also define it.
    expect(delegator).to_not_contain("pub fn " + name + "(")            check(delegator.contains("pub fn external_" + name + "("))
```

</details>

#### still exposes the short public names to existing importers via aliases

- still exposes the short public names to existing importers via aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still exposes the short public names to existing importers via aliases")
# The rename must not break the compatibility surface: every short name
# is re-exported from the small facade.
val facade = read_file("src/compiler/80.driver/driver_public_compile.spl")
for name in COLLIDING:
    check(facade.contains("external_" + name + " as " + name))
```

</details>

#### generalizes: no delegating facade redefines an in-process driver entry point

- generalizes: no delegating facade redefines an in-process driver entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generalizes: no delegating facade redefines an in-process driver entry point")
# Probes for the SAME class of cycle elsewhere — any other facade that
# spawns the `simple` CLI must not also define a name the in-process
# driver owns, or it can be dispatched to by an unrelated import.
val in_process = read_file("src/compiler/80.driver/driver_api_compile_single.spl")
val delegating = [
    "src/compiler/80.driver/driver_public_compile_process.spl",
    "src/compiler/80.driver/driver_public_compile_backends.spl",
    "src/compiler/80.driver/driver_public_compile_vhdl.spl"
]
for path in delegating:
    val source = read_file(path)
    if source.contains("rt_process_run(simple_bin"):
        for name in COLLIDING:
            if in_process.contains("pub fn " + name + "("):
                expect(source).to_not_contain("pub fn " + name + "(")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `2ad11cdbf4ba86e0d8d6cf7d4440d23193e454e8f208af03aa482504d22a4ae2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ad11cdbf4ba86e0d8d6cf7d4440d23193e454e8f208af03aa482504d22a4ae2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ad11cdbf4ba86e0d8d6cf7d4440d23193e454e8f208af03aa482504d22a4ae2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks spawning the bin/release/simple wrapper from a deployed release runtime with no marker set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks the wrapper by absolute path and from bootstrap-stage binaries too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still allows genuinely external binaries and unknown identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
