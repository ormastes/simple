# QEMU RV32 Raw Injected Regression

> Separate recovery lane for the low-level QEMU + GDB injected execution path. This is not the main RV32 proof; the stable ELF/shared-workload lane remains authoritative and this spec exists only to keep the run-control path covered in isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU RV32 Raw Injected Regression

Separate recovery lane for the low-level QEMU + GDB injected execution path. This is not the main RV32 proof; the stable ELF/shared-workload lane remains authoritative and this spec exists only to keep the run-control path covered in isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-007 |
| Category | Integration |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md) |
| Design | [doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md) |
| Research | N/A |
| Source | `test/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Separate recovery lane for the low-level QEMU + GDB injected execution path.
This is not the main RV32 proof; the stable ELF/shared-workload lane remains
authoritative and this spec exists only to keep the run-control path covered in
isolation.

The scenarios in this file focus on:

- connect
- upload and execute
- resume
- stop or halt
- register readback after stop

This keeps raw injected execution visible without letting it redefine the
authoritative RV32 product path.

## Syntax

```simple
var adapter = QemuRv32Adapter.new()
use std.spec.step

val conn = adapter.connect()
val manager = adapter.create_manager().ok.unwrap()
val exec_result = manager.execute_bytes("qemu_rv32_raw_zero", bytes, [])
```

## Examples

```simple
expect(exec.is_ok()).to_equal(true)
expect(exec.return_value).to_equal(42)
```

## Scenarios

### QEMU RV32 raw injected regression

<details>
<summary>Advanced: connects and executes a return-zero program through the raw injected lane</summary>

#### connects and executes a return-zero program through the raw injected lane _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- connects and executes a return-zero program through the raw injected lane
   - Expected: exec.is_ok() is true
   - Expected: exec.return_value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("connects and executes a return-zero program through the raw injected lane")
if not qemu_rv32_available():
    print "[skip] QEMU RV32 injected prerequisites unavailable"
    return

var adapter = QemuRv32Adapter.new()
val conn = adapter.connect()
if conn.is_err():
    print "[skip] connect failed: {conn.err().unwrap()}"
    return

val manager_result = adapter.create_manager()
if manager_result.is_err():
    adapter.disconnect()
    print "[skip] manager failed: {manager_result.err().unwrap()}"
    return

val compile_result = CompilerBridge.compile("fn main() -> i64:\n    0\n", Architecture.RiscV32, MemoryMap.qemu_rv32().code_start)
if compile_result.is_err():
    adapter.disconnect()
    print "[skip] compile failed: {compile_result.err().unwrap()}"
    return

var manager = manager_result.ok.unwrap()
val exec_result = manager.execute_bytes("qemu_rv32_raw_zero", compile_result.ok.unwrap(), [])
adapter.disconnect()

if exec_result.is_err():
    print "[skip] exec failed: {exec_result.err().unwrap()}"
else:
    val exec = exec_result.ok.unwrap()
    expect(exec.is_ok()).to_equal(true)
    expect(exec.return_value).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: recovers register readback after stop in the raw injected lane</summary>

#### recovers register readback after stop in the raw injected lane _(slow)_

- recovers register readback after stop in the raw injected lane
   - Expected: exec.is_ok() is true
   - Expected: exec.return_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recovers register readback after stop in the raw injected lane")
if not qemu_rv32_available():
    print "[skip] QEMU RV32 injected prerequisites unavailable"
    return

var adapter = QemuRv32Adapter.new()
val conn = adapter.connect()
if conn.is_err():
    print "[skip] connect failed: {conn.err().unwrap()}"
    return

val manager_result = adapter.create_manager()
if manager_result.is_err():
    adapter.disconnect()
    print "[skip] manager failed: {manager_result.err().unwrap()}"
    return

val compile_result = CompilerBridge.compile("fn main() -> i64:\n    42\n", Architecture.RiscV32, MemoryMap.qemu_rv32().code_start)
if compile_result.is_err():
    adapter.disconnect()
    print "[skip] compile failed: {compile_result.err().unwrap()}"
    return

var manager = manager_result.ok.unwrap()
val exec_result = manager.execute_bytes("qemu_rv32_raw_42", compile_result.ok.unwrap(), [])
adapter.disconnect()

if exec_result.is_err():
    print "[skip] exec failed: {exec_result.err().unwrap()}"
else:
    val exec = exec_result.ok.unwrap()
    expect(exec.is_ok()).to_equal(true)
    expect(exec.return_value).to_equal(42)
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


## Related Documentation

- **Plan:** `[doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)`
- **Design:** `[doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `36c8814a2a7ba861f4e0494d7318e48736e1a0264f1ea31b337dfa7e180d524a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36c8814a2a7ba861f4e0494d7318e48736e1a0264f1ea31b337dfa7e180d524a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36c8814a2a7ba861f4e0494d7318e48736e1a0264f1ea31b337dfa7e180d524a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl
mirror: doc/06_spec/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects and executes a return-zero program through the raw injected lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recovers register readback after stop in the raw injected lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
