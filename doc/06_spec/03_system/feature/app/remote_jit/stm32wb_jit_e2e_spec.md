# STM32WB Remote JIT End-to-End

> End-to-end JIT test on real STM32WB hardware via unified adapter pattern. Uses Stm32WbAdapter (OpenOCD + GDB MI) + CompilerBridge for compile-upload-execute.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- discovers required tools
   - Expected: command_available("openocd") is true
   - Expected: command_available("clang") is true
   - Expected: command_available("ld.lld") is true
   - Expected: command_available("llvm-objcopy") is true
   - Expected: stlink_detected() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("discovers required tools")
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

- connects to STM32WB via OpenOCD
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("connects to STM32WB via OpenOCD")
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

- compiles and uploads return-zero
   - Expected: exec.is_ok() is true
   - Expected: exec.return_value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles and uploads return-zero")
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

- compiles and executes return-42
   - Expected: exec.is_ok() is true
   - Expected: exec.return_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles and executes return-42")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `30876a6e83d21e8ac77ac6153bf9f62cd39199eaafa05d27fc124d873336f381`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `30876a6e83d21e8ac77ac6153bf9f62cd39199eaafa05d27fc124d873336f381`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `30876a6e83d21e8ac77ac6153bf9f62cd39199eaafa05d27fc124d873336f381`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.spl
mirror: doc/06_spec/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers required tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects to STM32WB via OpenOCD' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles and uploads return-zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
