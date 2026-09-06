# Riscv64 Ipc Destroy Port Specification

> Tests covering RV64 IpcDestroyPort.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Ipc Destroy Port Specification

## Scenarios

### RV64 IpcDestroyPort

#### allows a deny-all caller to self-revoke its anonymous reply port

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows a deny-all caller to self-revoke its anonymous reply port
   - Expected: destroyed.result.value equals `0`
   - Expected: destroyed.ipc.port_owner_task_id(port.id) equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allows a deny-all caller to self-revoke its anonymous reply port")
val scheduler = Scheduler.new()
var ipc = IpcManager.new()
val current = scheduler.get_current()
ipc.cap_manager.init_task(current, CapabilitySet.empty())
val port = ipc.create_port(current, "")

val destroyed = rv64_syscall_handler_state(destroy_port_args(port.id), scheduler, ipc, KernelLog.new(8))
expect(destroyed.result.value).to_equal(0)
expect(destroyed.ipc.port_owner_task_id(port.id)).to_equal(0u64)
```

</details>

#### rejects a wrong owner and missing port through the arch dispatcher

- rejects a wrong owner and missing port through the arch dispatcher
   - Expected: foreign.result.value equals `-1`
   - Expected: foreign.ipc.connect("foreign-rv64-port") != nil is true
   - Expected: missing.result.value equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a wrong owner and missing port through the arch dispatcher")
val scheduler = Scheduler.new()
var ipc = IpcManager.new()
val port = ipc.create_port(TaskId(id: 99), "foreign-rv64-port")

val foreign = rv64_syscall_handler_state(destroy_port_args(port.id), scheduler, ipc, KernelLog.new(8))
expect(foreign.result.value).to_equal(-1)
expect(foreign.ipc.connect("foreign-rv64-port") != nil).to_equal(true)
val missing = rv64_syscall_handler_state(destroy_port_args(999999u64), scheduler, foreign.ipc, KernelLog.new(8))
expect(missing.result.value).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV64 IpcDestroyPort.
- RV64 IpcDestroyPort

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2da18c70fe8a539433aba67c01ce09f91cbe8bef8b7f8c7e97a81b13d6587a7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2da18c70fe8a539433aba67c01ce09f91cbe8bef8b7f8c7e97a81b13d6587a7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2da18c70fe8a539433aba67c01ce09f91cbe8bef8b7f8c7e97a81b13d6587a7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows a deny-all caller to self-revoke its anonymous reply port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a wrong owner and missing port through the arch dispatcher' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
