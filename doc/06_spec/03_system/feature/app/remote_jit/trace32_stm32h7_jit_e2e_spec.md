# TRACE32 STM32H7 Remote JIT End-to-End

> Runs the real composite JIT lane for STM32H7 through the TRACE32 adapter path:

<!-- sdn-diagram:id=trace32_stm32h7_jit_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trace32_stm32h7_jit_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trace32_stm32h7_jit_e2e_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trace32_stm32h7_jit_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fixture_exists(RETURN_ZERO_FIXTURE)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: checks for a live TRACE32 Remote API session</summary>

#### checks for a live TRACE32 Remote API session _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
