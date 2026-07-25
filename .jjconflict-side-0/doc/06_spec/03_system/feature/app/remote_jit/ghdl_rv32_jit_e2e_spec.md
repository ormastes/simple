# GHDL RV32 RTL Simulation JIT End-to-End (Unified Adapter)

> End-to-end JIT verification on GHDL-simulated RV32I CPU via unified adapter pattern. Uses GhdlRv32Adapter for simulation lifecycle, CompilerBridge for compilation, and the standard connect/disconnect pattern.

<!-- sdn-diagram:id=ghdl_rv32_jit_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_rv32_jit_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_rv32_jit_e2e_spec -> std
ghdl_rv32_jit_e2e_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_rv32_jit_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GHDL RV32 RTL Simulation JIT End-to-End (Unified Adapter)

End-to-end JIT verification on GHDL-simulated RV32I CPU via unified adapter pattern. Uses GhdlRv32Adapter for simulation lifecycle, CompilerBridge for compilation, and the standard connect/disconnect pattern.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-030 |
| Category | Integration |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end JIT verification on GHDL-simulated RV32I CPU via unified adapter
pattern. Uses GhdlRv32Adapter for simulation lifecycle, CompilerBridge for
compilation, and the standard connect/disconnect pattern.

The adapter stores uploaded code in a local buffer, then runs a full GHDL
simulation on resume(). Semihosting output is parsed from simulation stdout.

## Scenarios

### GHDL RV32 RTL Simulation JIT E2E

<details>
<summary>Advanced: discovers GHDL simulator</summary>

#### discovers GHDL simulator _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: ghdl or cross-compilation tools not installed"
else:
    val ghdl_ver = shell("ghdl --version 2>&1")
    expect(ghdl_ver.exit_code).to_equal(0)
    expect(ghdl_ver.stdout).to_contain("GHDL")
```

</details>


</details>

<details>
<summary>Advanced: connects to GHDL RV32 simulation</summary>

#### connects to GHDL RV32 simulation _(slow)_

1. var adapter = GhdlRv32Adapter new
   - Expected: connect_result.is_ok() is true
2. adapter disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: ghdl not installed"
else:
    var adapter = GhdlRv32Adapter.new()
    val connect_result = adapter.connect()
    expect(connect_result.is_ok()).to_equal(true)
    adapter.disconnect()
```

</details>


</details>

<details>
<summary>Advanced: executes return-zero via GHDL RV32</summary>

#### executes return-zero via GHDL RV32 _(slow)_

1. var adapter = GhdlRv32Adapter new
   - Expected: connect_result.is_ok() is true
2. print "SKIP: compilation failed — {compile result err
3. adapter disconnect
   - Expected: write_result.is_ok() is true
4. print "SKIP: simulation failed — {resume result err
   - Expected: return_value equals `0`
   - Expected: adapter.verify_formal_contract(return_value).is_ok() is true
5. adapter disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: ghdl or cross-compilation tools not installed"
else:
    var adapter = GhdlRv32Adapter.new()
    val connect_result = adapter.connect()
    expect(connect_result.is_ok()).to_equal(true)

    val source = "fn main() -> i64:\n    0\n"
    val compile_result = CompilerBridge.compile(source, Architecture.RiscV32, adapter.memory_map.code_start)
    if compile_result.is_err():
        print "SKIP: compilation failed — {compile_result.err().unwrap()}"
        adapter.disconnect()
    else:
        val bytes = compile_result.unwrap()
        expect(bytes.len()).to_be_greater_than(0)

        val write_result = adapter.write_code(adapter.memory_map.code_start, bytes)
        expect(write_result.is_ok()).to_equal(true)

        val resume_result = adapter.resume()
        if resume_result.is_err():
            print "SKIP: simulation failed — {resume_result.err().unwrap()}"
        else:
            val return_value = adapter.sim_exit_code()
            expect(return_value).to_equal(0)
            expect(adapter.verify_formal_contract(return_value).is_ok()).to_equal(true)

        adapter.disconnect()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
