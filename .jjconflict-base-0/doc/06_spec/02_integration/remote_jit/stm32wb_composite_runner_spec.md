# STM32WB Baremetal Composite Runner

> Verifies JIT pipeline end-to-end on STM32WB via unified adapter.

<!-- sdn-diagram:id=stm32wb_composite_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32wb_composite_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32wb_composite_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32wb_composite_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STM32WB Baremetal Composite Runner

Verifies JIT pipeline end-to-end on STM32WB via unified adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/stm32wb_composite_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies JIT pipeline end-to-end on STM32WB via unified adapter.

## Scenarios

### STM32WB Baremetal Workload

<details>
<summary>Advanced: runs return-zero on STM32WB</summary>

#### runs return-zero on STM32WB _(slow)_

1. var adapter = Stm32WbAdapter new
2. print "[skip] connect failed: {conn err
3. adapter disconnect
4. adapter disconnect
5. var manager = mgr ok unwrap
6. adapter disconnect
7. print "[skip] exec failed: {result err
   - Expected: result.ok.unwrap().return_value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "[skip] STM32WB hardware not available"
    return
var adapter = Stm32WbAdapter.new()
val conn = adapter.connect()
if conn.is_err():
    print "[skip] connect failed: {conn.err().unwrap()}"
    return
val mgr = adapter.create_manager()
if mgr.is_err():
    adapter.disconnect()
    print "[skip] manager failed"
    return
val source = "fn main() -> i64:\n    0\n"
val limits = MemoryMap.stm32wb()
val compiled = CompilerBridge.compile(source, Architecture.Arm32, limits.code_start)
if compiled.is_err():
    adapter.disconnect()
    print "[skip] compile failed"
    return
var manager = mgr.ok.unwrap()
val result = manager.execute_bytes("workload_zero", compiled.ok.unwrap(), [])
adapter.disconnect()
if result.is_err():
    print "[skip] exec failed: {result.err().unwrap()}"
    return
expect(result.ok.unwrap().return_value).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: runs return-42 on STM32WB</summary>

#### runs return-42 on STM32WB _(slow)_

1. var adapter = Stm32WbAdapter new
2. print "[skip] connect failed: {conn err
3. adapter disconnect
4. adapter disconnect
5. var manager = mgr ok unwrap
6. adapter disconnect
7. print "[skip] exec failed: {result err
   - Expected: result.ok.unwrap().return_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "[skip] STM32WB hardware not available"
    return
var adapter = Stm32WbAdapter.new()
val conn = adapter.connect()
if conn.is_err():
    print "[skip] connect failed: {conn.err().unwrap()}"
    return
val mgr = adapter.create_manager()
if mgr.is_err():
    adapter.disconnect()
    print "[skip] manager failed"
    return
val source = "fn main() -> i64:\n    42\n"
val limits = MemoryMap.stm32wb()
val compiled = CompilerBridge.compile(source, Architecture.Arm32, limits.code_start)
if compiled.is_err():
    adapter.disconnect()
    print "[skip] compile failed"
    return
var manager = mgr.ok.unwrap()
val result = manager.execute_bytes("workload_42", compiled.ok.unwrap(), [])
adapter.disconnect()
if result.is_err():
    print "[skip] exec failed: {result.err().unwrap()}"
    return
expect(result.ok.unwrap().return_value).to_equal(42)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
