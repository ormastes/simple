# TRACE32 STM32H7 Remote JIT End-to-End

> Runs the real composite JIT lane for STM32H7 through the TRACE32 adapter path:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TRACE32 STM32H7 Remote JIT End-to-End

Runs the real composite JIT lane for STM32H7 through the TRACE32 adapter path:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TRACE32-JIT-STM32H7 |
| Category | Integration |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the real composite JIT lane for STM32H7 through the TRACE32 adapter path:

- `run_test_file_composite`
- `Trace32Adapter`
- `T32GdbBridgeClient`
- `RemoteExecutionManager`

Requires a live TRACE32 PowerView session with the repo GDB bridge on `2331`.

## Environment

- TRACE32 PowerView reachable on Remote API port `20000`
- TRACE32 GDB bridge reachable on TCP port `2331`
- LLVM host tools available: `clang`, `ld.lld`, `llvm-objcopy`
- Fixture file present: `test/fixtures/remote_jit/stm32h7_return_zero.spl`

## Behavior

- Verifies fixture discovery before attempting live hardware access
- Separately checks Remote API reachability and GDB bridge readiness
- Executes the real composite JIT lane only when all prerequisites are present
- Emits `[skip]` messages instead of failing when the external lab environment is unavailable

## Execution Notes

- This is an environment-backed integration test, not a hermetic unit test
- Successful execution proves the repo default TRACE32 STM32H7 lane is callable end-to-end
- A skipped run documents missing infrastructure rather than a product regression

## Scenarios

### TRACE32 STM32H7 JIT E2E

<details>
<summary>Advanced: discovers the repo return-zero fixture</summary>

#### discovers the repo return-zero fixture _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- discovers the repo return-zero fixture
   - Expected: fixture_exists(RETURN_ZERO_FIXTURE) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("discovers the repo return-zero fixture")
expect(fixture_exists(RETURN_ZERO_FIXTURE)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: checks for a live TRACE32 Remote API session</summary>

#### checks for a live TRACE32 Remote API session _(slow)_

- checks for a live TRACE32 Remote API session
   - Expected: t32_reachable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for a live TRACE32 Remote API session")
if t32_reachable():
    expect(t32_reachable()).to_equal(true)
    print "[ok] TRACE32 PowerView responds to PING"
else:
    print "[skip] TRACE32 PowerView not reachable on port 20000"
```

</details>


</details>

<details>
<summary>Advanced: checks for a live TRACE32 GDB bridge on the repo default port</summary>

#### checks for a live TRACE32 GDB bridge on the repo default port _(slow)_

- checks for a live TRACE32 GDB bridge on the repo default port
   - Expected: t32_gdb_bridge_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for a live TRACE32 GDB bridge on the repo default port")
if t32_reachable() and t32_gdb_bridge_ready():
    expect(t32_gdb_bridge_ready()).to_equal(true)
    print "[ok] TRACE32 GDB bridge responds on port 2331"
else:
    print "[skip] TRACE32 GDB bridge not reachable"
```

</details>


</details>

<details>
<summary>Advanced: runs the real composite TRACE32 STM32H7 JIT lane</summary>

#### runs the real composite TRACE32 STM32H7 JIT lane _(slow)_

- runs the real composite TRACE32 STM32H7 JIT lane
   - Expected: result.failed equals `0`
   - Expected: result.error equals ``
   - Expected: result.passed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the real composite TRACE32 STM32H7 JIT lane")
if live_trace32_ready():
    val options = trace32_h7_options(RETURN_ZERO_FIXTURE)
    val result = run_test_file_composite(RETURN_ZERO_FIXTURE, options, TRACE32_STM32H7_SPEC)
    expect(result.failed).to_equal(0)
    expect(result.error).to_equal("")
    expect(result.passed).to_equal(1)
    print "[ok] TRACE32 STM32H7 composite JIT returned 0"
else:
    print "[skip] TRACE32 session, GDB bridge, toolchain, or fixture not available"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
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

- Canonical SPipe generation for source `d8b6aa2e927f743f25f3c7ad9f6f98cb7d22b7757466630beea0dbe4d76c795e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d8b6aa2e927f743f25f3c7ad9f6f98cb7d22b7757466630beea0dbe4d76c795e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d8b6aa2e927f743f25f3c7ad9f6f98cb7d22b7757466630beea0dbe4d76c795e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl
mirror: doc/06_spec/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers the repo return-zero fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks for a live TRACE32 Remote API session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks for a live TRACE32 GDB bridge on the repo default port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
