*Source: `test/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl`*  
*Last Updated: 2026-03-31*

---

# QEMU RV32 Raw Injected Regression

**Feature IDs:** #RJE-007  
**Category:** Integration  
**Difficulty:** 4/5  
**Status:** Implemented  
**Requirements:** N/A  
**Plan:** [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)  
**Design:** [doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md)  
**Research:** N/A

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
val conn = adapter.connect()
val manager = adapter.create_manager().ok.unwrap()
val exec_result = manager.execute_bytes("qemu_rv32_raw_zero", bytes, [])
```

## Examples

```simple
expect(exec.is_ok()).to_equal(true)
expect(exec.return_value).to_equal(42)
```
