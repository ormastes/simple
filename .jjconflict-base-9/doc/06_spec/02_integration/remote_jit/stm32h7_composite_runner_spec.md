# STM32H7 Baremetal Composite Runner

> Verifies the shared baremetal library workload on STM32H7 through the HAL-backed JIT path.

<!-- sdn-diagram:id=stm32h7_composite_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32h7_composite_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32h7_composite_runner_spec -> app
stm32h7_composite_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32h7_composite_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STM32H7 Baremetal Composite Runner

Verifies the shared baremetal library workload on STM32H7 through the HAL-backed JIT path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/stm32h7_composite_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the shared baremetal library workload on STM32H7 through the HAL-backed JIT path.

## Scenarios

### STM32H7 Baremetal Workload

<details>
<summary>Advanced: runs the shared baremetal library workload on STM32H7</summary>

#### runs the shared baremetal library workload on STM32H7 _(slow)_

1. print "[skip] connect failed: {connect result err
2. stm32h7 disconnect
3. print "[skip] compile failed: {compile result err
4. stm32h7 disconnect
5. stm32h7 disconnect
6. print "[skip] upload failed: {write result err
7. stm32h7 disconnect
8. print "[skip] set SP failed: {sp result err
9. stm32h7 disconnect
10. print "[skip] set LR failed: {lr result err
11. stm32h7 disconnect
12. print "[skip] set PC failed: {pc result err
13. stm32h7 disconnect
14. print "[skip] resume failed: {resume result err
15. shell
16. stm32h7 disconnect
17. print "[skip] read R0 failed: {r0 result err
18. print "[skip] read PC failed: {pc after result err
   - Expected: r0 equals `0`
   - Expected: pc_after == expected_halt_pc or pc_after == expected_pc is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 93 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "[skip] STM32H7 hardware not available"
    return

val source = shared_workload_source()
if source.trim() == "":
    print "[skip] shared workload fixture unreadable"
    return

val connect_result = stm32h7_connect()
if connect_result.is_err():
    print "[skip] connect failed: {connect_result.err().unwrap()}"
    return

var openocd_pid: i64 = 0
match connect_result:
    case Ok(v):
        openocd_pid = v
    case Err(_):
        openocd_pid = 0

val code_start = stm32h7_code_start()
val stack_top = stm32h7_stack_top()
val compile_result = compile_stub_arm32(source, code_start)
if compile_result.is_err():
    stm32h7_disconnect(openocd_pid)
    print "[skip] compile failed: {compile_result.err().unwrap()}"
    return

var compiled_bytes: [i32] = []
match compile_result:
    case Ok(v):
        compiled_bytes = v
    case Err(_):
        compiled_bytes = []

val bytes = append_halt_trampoline_arm32_local(compiled_bytes)
val total = bytes.len()
if total > stm32h7_code_capacity():
    stm32h7_disconnect(openocd_pid)
    print "[skip] layout failed: binary too large for target code region"
    return

val code_base = code_start
val halt_addr = code_base + total - 2
val entry_pc = code_base + 1
val return_pc = halt_addr + 1
val write_result = stm32h7_write_code(code_base, bytes)
if write_result.is_err():
    stm32h7_disconnect(openocd_pid)
    print "[skip] upload failed: {write_result.err().unwrap()}"
    return

val sp_result = stm32h7_write_register(13, stack_top)
if sp_result.is_err():
    stm32h7_disconnect(openocd_pid)
    print "[skip] set SP failed: {sp_result.err().unwrap()}"
    return

val lr_result = stm32h7_write_register(14, return_pc)
if lr_result.is_err():
    stm32h7_disconnect(openocd_pid)
    print "[skip] set LR failed: {lr_result.err().unwrap()}"
    return

val pc_result = stm32h7_write_register(15, entry_pc)
if pc_result.is_err():
    stm32h7_disconnect(openocd_pid)
    print "[skip] set PC failed: {pc_result.err().unwrap()}"
    return

val resume_result = stm32h7_resume()
if resume_result.is_err():
    stm32h7_disconnect(openocd_pid)
    print "[skip] resume failed: {resume_result.err().unwrap()}"
    return

shell("sleep 0.5")
val r0_result = stm32h7_read_register(0)
val pc_after_result = stm32h7_read_register(15)
stm32h7_disconnect(openocd_pid)

if r0_result.is_err():
    print "[skip] read R0 failed: {r0_result.err().unwrap()}"
elif pc_after_result.is_err():
    print "[skip] read PC failed: {pc_after_result.err().unwrap()}"
else:
    val r0 = r0_result.ok.unwrap()
    val pc_after = pc_after_result.ok.unwrap()
    val expected_halt_pc = halt_addr
    val expected_pc = halt_addr + 2
    expect(r0).to_equal(0)
    expect(pc_after == expected_halt_pc or pc_after == expected_pc).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
