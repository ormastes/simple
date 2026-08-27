# SimpleOS Desktop Core Formal Verification Contract

> This pure system spec covers the bounded desktop-core verification surface: RISC-V user/kernel context separation, trap classification, syscall argument marshalling, desktop app-switcher selection, and crash-domain policy. Unexpected enum branches assert the expected enum/domain value directly so failures report which contract value drifted.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Desktop Core Formal Verification Contract

This pure system spec covers the bounded desktop-core verification surface: RISC-V user/kernel context separation, trap classification, syscall argument marshalling, desktop app-switcher selection, and crash-domain policy. Unexpected enum branches assert the expected enum/domain value directly so failures report which contract value drifted.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This pure system spec covers the bounded desktop-core verification surface:
RISC-V user/kernel context separation, trap classification, syscall argument
marshalling, desktop app-switcher selection, and crash-domain policy. Unexpected
enum branches assert the expected enum/domain value directly so failures report
which contract value drifted.

## Scenarios

### simpleos_desktop_core_formal_verification feature spec

#### REQ-SODCFV-002 keeps kernel and user privilege return state distinct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-SODCFV-002 keeps kernel and user privilege return state distinct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-SODCFV-002 keeps kernel and user privilege return state distinct")
val kernel_ctx = create_rv64_kernel_context(0x80200000, 0x80400000, 0)
val user_ctx = create_rv64_user_context(0x400000, 0x410000, 0)
assert_not_equal((kernel_ctx.sstatus & RV64_SSTATUS_SPP), 0)
assert_equal(user_ctx.sstatus & RV64_SSTATUS_SPP, 0)
```

</details>

#### REQ-SODCFV-002 preserves user ecall and external interrupt as different kernel-core paths

- REQ-SODCFV-002 preserves user ecall and external interrupt as different kernel-core paths
   - Expected: RV64_CAUSE_ECALL_FROM_U equals `8`
   - Expected: syscall_kind equals `Rv64TrapKind.UserEcall`
   - Expected: irq_cause & 0x7FFFFFFFFFFFFFFF equals `RV64_CAUSE_S_EXTERNAL_INTERRUPT`
   - Expected: irq_kind equals `Rv64TrapKind.ExternalInterrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-SODCFV-002 preserves user ecall and external interrupt as different kernel-core paths")
val irq_cause = RV64_CAUSE_INTERRUPT_BIT + RV64_CAUSE_S_EXTERNAL_INTERRUPT
val syscall_kind = classify_rv64_trap(RV64_CAUSE_ECALL_FROM_U)
val irq_kind = classify_rv64_trap(irq_cause)
match syscall_kind:
    case Rv64TrapKind.UserEcall:
        expect(RV64_CAUSE_ECALL_FROM_U).to_equal(8)
        assert_equal(RV64_CAUSE_ECALL_FROM_U & RV64_CAUSE_INTERRUPT_BIT, 0)
    case _:
        expect(syscall_kind).to_equal(Rv64TrapKind.UserEcall)
match irq_kind:
    case Rv64TrapKind.ExternalInterrupt:
        assert_not_equal((irq_cause & RV64_CAUSE_INTERRUPT_BIT), 0)
        expect(irq_cause & 0x7FFFFFFFFFFFFFFF).to_equal(RV64_CAUSE_S_EXTERNAL_INTERRUPT)
    case _:
        expect(irq_kind).to_equal(Rv64TrapKind.ExternalInterrupt)
```

</details>

#### REQ-SODCFV-002 keeps syscall register marshalling stable

- REQ-SODCFV-002 keeps syscall register marshalling stable
   - Expected: args.id equals `77`
   - Expected: args.arg0 equals `11`
   - Expected: args.arg5 equals `66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-SODCFV-002 keeps syscall register marshalling stable")
val ctx = Riscv64Context(
    ra: 0, sp: 0, gp: 0, tp: 0,
    t0: 0, t1: 0, t2: 0,
    s0: 0, s1: 0,
    a0: 11, a1: 22, a2: 33, a3: 44, a4: 55, a5: 66, a6: 0, a7: 77,
    s2: 0, s3: 0, s4: 0, s5: 0, s6: 0, s7: 0, s8: 0, s9: 0, s10: 0, s11: 0,
    t3: 0, t4: 0, t5: 0, t6: 0,
    sepc: 0x1000,
    sstatus: 0,
    scause: RV64_CAUSE_ECALL_FROM_U,
    fp_state: ExtendedCtxRv(bytes: [0; 264]),
    fp_pad: 0
)
val args = rv64_syscall_args_from_context(ctx)
expect(args.id).to_equal(77)
expect(args.arg0).to_equal(11)
expect(args.arg5).to_equal(66)
```

</details>

#### REQ-SODCFV-003 keeps desktop selection unique and updates it after close

- REQ-SODCFV-003 keeps desktop selection unique and updates it after close
   - Expected: switcher.is_visible() is true
   - Expected: switcher.get_selected_window_id()?.value equals `10`
   - Expected: switcher.get_selected_window_id()?.value equals `20`
   - Expected: closed?.value equals `20`
   - Expected: switcher.get_selected_window_id()?.value equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-SODCFV-003 keeps desktop selection unique and updates it after close")
var switcher = AppSwitcher.create(Px(value: 1280), Px(value: 720))
switcher.show(
    [WindowId(value: 10), WindowId(value: 20)],
    ["Terminal", "Browser"]
)
expect(switcher.is_visible()).to_equal(true)
expect(switcher.get_selected_window_id()?.value).to_equal(10)
switcher.select_next()
expect(switcher.get_selected_window_id()?.value).to_equal(20)
val closed = switcher.close_selected()
expect(closed?.value).to_equal(20)
expect(switcher.get_selected_window_id()?.value).to_equal(10)
```

</details>

#### REQ-SODCFV-003 and NFR-SODCFV-008 keep user apps and kernel components in different crash domains

- REQ-SODCFV-003 and NFR-SODCFV-008 keep user apps and kernel components in different crash domains
   - Expected: user_policy.max_restarts equals `1`
   - Expected: user_policy.quarantine_on_limit is true
   - Expected: user_domain equals `AppFaultDomain.Process`
   - Expected: kernel_policy.max_restarts equals `0`
   - Expected: kernel_policy.quarantine_on_limit is false
   - Expected: kernel_domain equals `AppFaultDomain.KernelResident`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-SODCFV-003 and NFR-SODCFV-008 keep user apps and kernel components in different crash domains")
val user_domain = default_fault_domain(AppClass.UserApp)
val kernel_domain = default_fault_domain(AppClass.KernelComponent)
match user_domain:
    case AppFaultDomain.Process:
        val user_policy = default_supervisor_policy(AppClass.UserApp)
        expect(user_policy.max_restarts).to_equal(1)
        expect(user_policy.quarantine_on_limit).to_equal(true)
    case _:
        expect(user_domain).to_equal(AppFaultDomain.Process)
match kernel_domain:
    case AppFaultDomain.KernelResident:
        val kernel_policy = default_supervisor_policy(AppClass.KernelComponent)
        expect(kernel_policy.max_restarts).to_equal(0)
        expect(kernel_policy.quarantine_on_limit).to_equal(false)
    case _:
        expect(kernel_domain).to_equal(AppFaultDomain.KernelResident)
```

</details>

#### REQ-SODCFV-003 keeps restart policy stricter for user apps than for kernel components

- REQ-SODCFV-003 keeps restart policy stricter for user apps than for kernel components
   - Expected: user_policy.max_restarts equals `1`
   - Expected: kernel_policy.max_restarts equals `0`
   - Expected: user_policy.quarantine_on_limit is true
   - Expected: kernel_policy.quarantine_on_limit is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-SODCFV-003 keeps restart policy stricter for user apps than for kernel components")
val user_policy = default_supervisor_policy(AppClass.UserApp)
val kernel_policy = default_supervisor_policy(AppClass.KernelComponent)
expect(user_policy.max_restarts).to_equal(1)
expect(kernel_policy.max_restarts).to_equal(0)
expect(user_policy.quarantine_on_limit).to_equal(true)
expect(kernel_policy.quarantine_on_limit).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
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

- Canonical SPipe generation for source `7097e8e0f6bd8b8ce0a86e59bb7810f984396aec4e3c1ce12a1934d20b07b3cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7097e8e0f6bd8b8ce0a86e59bb7810f984396aec4e3c1ce12a1934d20b07b3cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7097e8e0f6bd8b8ce0a86e59bb7810f984396aec4e3c1ce12a1934d20b07b3cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl
mirror: doc/06_spec/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SODCFV-002 keeps kernel and user privilege return state distinct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SODCFV-002 preserves user ecall and external interrupt as different kernel-core paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SODCFV-002 keeps syscall register marshalling stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
