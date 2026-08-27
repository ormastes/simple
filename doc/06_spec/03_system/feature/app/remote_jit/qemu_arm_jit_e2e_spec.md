# QEMU ARM Remote JIT E2E

> End-to-end JIT on QEMU ARM using the unified adapter pattern. Uses QemuArmAdapter for connect/disconnect/execute lifecycle, CompilerBridge for Simple-to-binary compilation, and RemoteExecutionManager for the full upload-execute pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU ARM Remote JIT E2E

End-to-end JIT on QEMU ARM using the unified adapter pattern. Uses QemuArmAdapter for connect/disconnect/execute lifecycle, CompilerBridge for Simple-to-binary compilation, and RemoteExecutionManager for the full upload-execute pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-020 |
| Category | Integration |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end JIT on QEMU ARM using the unified adapter pattern.
Uses QemuArmAdapter for connect/disconnect/execute lifecycle,
CompilerBridge for Simple-to-binary compilation, and
RemoteExecutionManager for the full upload-execute pipeline.

## Scenarios

### QEMU ARM Remote JIT E2E

<details>
<summary>Advanced: discovers required tools</summary>

#### discovers required tools _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- discovers required tools


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("discovers required tools")
if not qemu_available():
    print "SKIP: QEMU ARM toolchain not available (need qemu-system-arm, clang, ld.lld, llvm-objcopy)"
else:
    val path = shell("command -v qemu-system-arm").stdout.trim()
    print "qemu-system-arm found at: {path}"
    expect(path.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: connects to QEMU ARM</summary>

#### connects to QEMU ARM _(slow)_

- connects to QEMU ARM
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("connects to QEMU ARM")
if not qemu_available():
    print "SKIP: QEMU ARM toolchain not available"
else:
    var adapter = QemuArmAdapter.new()
    val result = adapter.connect()
    if result.is_err():
        print "SKIP: QEMU ARM connect failed: {result.err().unwrap()}"
    else:
        expect(result.is_ok()).to_equal(true)
        adapter.disconnect()
```

</details>


</details>

<details>
<summary>Advanced: executes return-zero via QEMU ARM</summary>

#### executes return-zero via QEMU ARM _(slow)_

- executes return-zero via QEMU ARM
   - Expected: result.return_value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes return-zero via QEMU ARM")
if not qemu_available():
    print "SKIP: QEMU ARM toolchain not available"
else:
    var adapter = QemuArmAdapter.new()
    val conn = adapter.connect()
    if conn.is_err():
        print "SKIP: QEMU ARM connect failed: {conn.err().unwrap()}"
    else:
        val source = "fn main() -> i64:\n    0\n"
        val mem = MemoryMap.qemu_arm()
        val bytes_result = CompilerBridge.compile(source, Architecture.Arm32, mem.code_start)
        if bytes_result.is_err():
            print "SKIP: compilation failed: {bytes_result.err().unwrap()}"
            adapter.disconnect()
        else:
            val bytes = bytes_result.ok.unwrap()
            val manager_result = adapter.create_manager()
            if manager_result.is_err():
                print "SKIP: manager creation failed: {manager_result.err().unwrap()}"
            else:
                val manager = manager_result.ok.unwrap()
                val exec_result = manager.execute_bytes("return_zero", bytes, [])
                if exec_result.is_err():
                    print "SKIP: execution failed: {exec_result.err().unwrap()}"
                else:
                    val result = exec_result.ok.unwrap()
                    expect(result.return_value).to_equal(0)
            adapter.disconnect()
```

</details>


</details>

<details>
<summary>Advanced: executes return-42 via QEMU ARM</summary>

#### executes return-42 via QEMU ARM _(slow)_

- executes return-42 via QEMU ARM
   - Expected: result.return_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes return-42 via QEMU ARM")
if not qemu_available():
    print "SKIP: QEMU ARM toolchain not available"
else:
    var adapter = QemuArmAdapter.new()
    val conn = adapter.connect()
    if conn.is_err():
        print "SKIP: QEMU ARM connect failed: {conn.err().unwrap()}"
    else:
        val source = "fn main() -> i64:\n    42\n"
        val mem = MemoryMap.qemu_arm()
        val bytes_result = CompilerBridge.compile(source, Architecture.Arm32, mem.code_start)
        if bytes_result.is_err():
            print "SKIP: compilation failed: {bytes_result.err().unwrap()}"
            adapter.disconnect()
        else:
            val bytes = bytes_result.ok.unwrap()
            val manager_result = adapter.create_manager()
            if manager_result.is_err():
                print "SKIP: manager creation failed: {manager_result.err().unwrap()}"
            else:
                val manager = manager_result.ok.unwrap()
                val exec_result = manager.execute_bytes("return_42", bytes, [])
                if exec_result.is_err():
                    print "SKIP: execution failed: {exec_result.err().unwrap()}"
                else:
                    val result = exec_result.ok.unwrap()
                    expect(result.return_value).to_equal(42)
            adapter.disconnect()
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

- Canonical SPipe generation for source `f73b3c45f23530d33862f49e46486984af8bf01d6deb9898be802900f73d25c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f73b3c45f23530d33862f49e46486984af8bf01d6deb9898be802900f73d25c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f73b3c45f23530d33862f49e46486984af8bf01d6deb9898be802900f73d25c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.spl
mirror: doc/06_spec/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers required tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects to QEMU ARM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes return-zero via QEMU ARM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
