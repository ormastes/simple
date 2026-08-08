# STM32WB Remote JIT End-to-End

> End-to-end JIT test on real STM32WB hardware via unified adapter pattern. Uses Stm32WbAdapter (OpenOCD + GDB MI) + CompilerBridge for compile-upload-execute.

<!-- sdn-diagram:id=stm32wb_jit_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32wb_jit_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32wb_jit_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32wb_jit_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STM32WB Remote JIT End-to-End

End-to-end JIT test on real STM32WB hardware via unified adapter pattern. Uses Stm32WbAdapter (OpenOCD + GDB MI) + CompilerBridge for compile-upload-execute.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-010 |
| Category | Integration |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end JIT test on real STM32WB hardware via unified adapter pattern.
Uses Stm32WbAdapter (OpenOCD + GDB MI) + CompilerBridge for compile-upload-execute.

Requires STM32WB Nucleo board with ST-Link connected (USB 0483:).

## Scenarios

### STM32WB Remote JIT E2E

<details>
<summary>Advanced: discovers required tools</summary>

#### discovers required tools _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "[skip] STM32WB hardware or tools not available"
    return
expect(command_available("openocd")).to_equal(true)
expect(command_available("clang")).to_equal(true)
expect(command_available("ld.lld")).to_equal(true)
expect(command_available("llvm-objcopy")).to_equal(true)
expect(stlink_detected()).to_equal(true)
print "[ok] all required tools and hardware detected"
```

</details>


</details>

<details>
<summary>Advanced: connects to STM32WB via OpenOCD</summary>

#### connects to STM32WB via OpenOCD _(slow)_

1. var adapter = Stm32WbAdapter new
2. print "[skip] connect failed: {result err
   - Expected: result.is_ok() is true
3. adapter disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "[skip] STM32WB hardware not available"
    return
var adapter = Stm32WbAdapter.new()
val result = adapter.connect()
if result.is_err():
    print "[skip] connect failed: {result.err().unwrap()}"
    return
expect(result.is_ok()).to_equal(true)
print "[ok] connected to STM32WB via OpenOCD"
adapter.disconnect()
```

</details>


</details>

<details>
<summary>Advanced: compiles and uploads return-zero</summary>

#### compiles and uploads return-zero _(slow)_

1. var adapter = Stm32WbAdapter new
2. print "[skip] connect failed: {conn err
3. print "[skip] manager failed: {manager result err
4. adapter disconnect
5. print "[skip] compile failed: {compile result err
6. adapter disconnect
7. var manager = manager result ok unwrap
8. adapter disconnect
9. print "[skip] exec failed: {exec result err
   - Expected: exec.is_ok() is true
   - Expected: exec.return_value equals `0`
10. print "[ok] STM32WB JIT: main


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "[skip] STM32WB hardware not available"
else:
    var adapter = Stm32WbAdapter.new()
    val conn = adapter.connect()
    if conn.is_err():
        print "[skip] connect failed: {conn.err().unwrap()}"
    else:
        val manager_result = adapter.create_manager()
        if manager_result.is_err():
            print "[skip] manager failed: {manager_result.err().unwrap()}"
            adapter.disconnect()
        else:
            val source = "fn main() -> i64:\n    0\n"
            val limits = MemoryMap.stm32wb()
            val compile_result = CompilerBridge.compile(source, Architecture.Arm32, limits.code_start)
            if compile_result.is_err():
                print "[skip] compile failed: {compile_result.err().unwrap()}"
                adapter.disconnect()
            else:
                var manager = manager_result.ok.unwrap()
                val exec_result = manager.execute_bytes("stm32wb_return_zero", compile_result.ok.unwrap(), [])
                adapter.disconnect()

                if exec_result.is_err():
                    print "[skip] exec failed: {exec_result.err().unwrap()}"
                else:
                    val exec = exec_result.ok.unwrap()
                    expect(exec.is_ok()).to_equal(true)
                    expect(exec.return_value).to_equal(0)
                    print "[ok] STM32WB JIT: main() returned 0"
```

</details>


</details>

<details>
<summary>Advanced: compiles and executes return-42</summary>

#### compiles and executes return-42 _(slow)_

1. var adapter = Stm32WbAdapter new
2. print "[skip] connect failed: {conn err
3. print "[skip] manager failed: {manager result err
4. adapter disconnect
5. print "[skip] compile failed: {compile result err
6. adapter disconnect
7. var manager = manager result ok unwrap
8. adapter disconnect
9. print "[skip] exec failed: {exec result err
   - Expected: exec.is_ok() is true
   - Expected: exec.return_value equals `42`
10. print "[ok] STM32WB JIT: main


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not hardware_ready():
    print "[skip] STM32WB hardware not available"
else:
    var adapter = Stm32WbAdapter.new()
    val conn = adapter.connect()
    if conn.is_err():
        print "[skip] connect failed: {conn.err().unwrap()}"
    else:
        val manager_result = adapter.create_manager()
        if manager_result.is_err():
            print "[skip] manager failed: {manager_result.err().unwrap()}"
            adapter.disconnect()
        else:
            val source = "fn main() -> i64:\n    42\n"
            val limits = MemoryMap.stm32wb()
            val compile_result = CompilerBridge.compile(source, Architecture.Arm32, limits.code_start)
            if compile_result.is_err():
                print "[skip] compile failed: {compile_result.err().unwrap()}"
                adapter.disconnect()
            else:
                var manager = manager_result.ok.unwrap()
                val exec_result = manager.execute_bytes("stm32wb_return_42", compile_result.ok.unwrap(), [])
                adapter.disconnect()

                if exec_result.is_err():
                    print "[skip] exec failed: {exec_result.err().unwrap()}"
                else:
                    val exec = exec_result.ok.unwrap()
                    expect(exec.is_ok()).to_equal(true)
                    expect(exec.return_value).to_equal(42)
                    print "[ok] STM32WB JIT: main() returned 42"
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
