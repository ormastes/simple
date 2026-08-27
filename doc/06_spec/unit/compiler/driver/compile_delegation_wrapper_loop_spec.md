# compile_delegation_wrapper_loop_spec

> Purpose and audience: owning engineering team verifying release-wrapper self-delegation (delegation-loop regression).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# compile_delegation_wrapper_loop_spec

Purpose and audience: owning engineering team verifying release-wrapper self-delegation (delegation-loop regression).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: owning engineering team verifying release-wrapper self-delegation (delegation-loop regression).

## Scenarios

### release-wrapper self-delegation (delegation-loop regression)

#### blocks spawning the bin/release/simple wrapper from a deployed release runtime with no marker set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocks spawning the bin/release/simple wrapper from a deployed release runtime with no marker set


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks spawning the bin/release/simple wrapper from a deployed release runtime with no marker set")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks the wrapper by absolute path and from bootstrap-stage binaries too")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still allows genuinely external binaries and unknown identities")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards every rt_process_run(simple_bin, ...) call site with the delegation guard")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the lightweight facade lightweight: it never loads the full in-process driver")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# The delegating facade must stay a pure process-spawner. Importing the
# full driver here would make every selective import evaluate the whole
# compiler graph under the test interpreter.
val source = read_file("src/compiler/80.driver/driver_public_compile_process.spl")
assert_equal(source.contains("use lazy compiler.driver.driver_api_compile_single"), false)
assert_equal(source.contains("compiler_driver_create"), false)
```

</details>

#### fires the wrapper rule inside the full decision core, not only the helper

- fires the wrapper rule inside the full decision core, not only the helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fires the wrapper rule inside the full decision core, not only the helper")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines every delegating entry point under a distinct external_ name")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val delegator = read_file("src/compiler/80.driver/driver_public_compile_process.spl")
val in_process = read_file("src/compiler/80.driver/driver_api_compile_single.spl")
for name in COLLIDING:
    # The in-process driver keeps the short name...
    check(in_process.contains("pub fn " + name + "("))
    # ...and the delegator must NOT also define it.
    assert_equal(delegator.contains("pub fn " + name + "("), false)
    check(delegator.contains("pub fn external_" + name + "("))
```

</details>

#### still exposes the short public names to existing importers via aliases

- still exposes the short public names to existing importers via aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still exposes the short public names to existing importers via aliases")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generalizes: no delegating facade redefines an in-process driver entry point")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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
                assert_equal(source.contains("pub fn " + name + "("), false)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `853105de07a1610be854a3515bcbd406afa132aa0b09811d5f6d746ace72d930`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `853105de07a1610be854a3515bcbd406afa132aa0b09811d5f6d746ace72d930`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `853105de07a1610be854a3515bcbd406afa132aa0b09811d5f6d746ace72d930`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl
mirror: doc/06_spec/unit/compiler/driver/compile_delegation_wrapper_loop_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/driver/compile_delegation_wrapper_loop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/driver/compile_delegation_wrapper_loop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
