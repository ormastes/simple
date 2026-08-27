# GHDL RV32 RTL Simulation JIT End-to-End (Unified Adapter)

> End-to-end JIT verification on GHDL-simulated RV32I CPU via unified adapter pattern. Uses GhdlRv32Adapter for simulation lifecycle, CompilerBridge for compilation, and the standard connect/disconnect pattern.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- discovers GHDL simulator
   - Expected: ghdl_ver.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("discovers GHDL simulator")
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

- connects to GHDL RV32 simulation
   - Expected: connect_result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("connects to GHDL RV32 simulation")
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

- executes return-zero via GHDL RV32
   - Expected: connect_result.is_ok() is true
   - Expected: write_result.is_ok() is true
   - Expected: return_value equals `0`
   - Expected: adapter.verify_formal_contract(return_value).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes return-zero via GHDL RV32")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ba2070d9215d34073870f245ac074c9bbaa746b711a76e1670708e26c9b5516`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ba2070d9215d34073870f245ac074c9bbaa746b711a76e1670708e26c9b5516`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ba2070d9215d34073870f245ac074c9bbaa746b711a76e1670708e26c9b5516`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.spl
mirror: doc/06_spec/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers GHDL simulator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects to GHDL RV32 simulation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes return-zero via GHDL RV32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
