# RTOS Timer Configuration Specification

> Verifies RTOS timer arch constants, register addresses, and TimerConfig

<!-- sdn-diagram:id=timer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=timer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

timer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=timer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RTOS Timer Configuration Specification

Verifies RTOS timer arch constants, register addresses, and TimerConfig

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure  **Difficulty:** 2/5  **Status:** Implemented |
| Status | Active |
| Source | `test/01_unit/os/realtime/timer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies RTOS timer arch constants, register addresses, and TimerConfig
construction. Hardware calls cannot run in interpreter mode.

## Scenarios

### Timer Architecture Constants

#### defines ARM as arch 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TIMER_ARCH_ARM).to_equal(0)
```

</details>

#### defines RISC-V as arch 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TIMER_ARCH_RISCV).to_equal(1)
```

</details>

#### defines x86_64 as arch 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TIMER_ARCH_X86_64).to_equal(2)
```

</details>

### Timer Register Addresses

#### ARM SysTick CSR is at 0xE000E010

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SYSTICK_CSR).to_equal(0xE000E010)
```

</details>

#### ARM SysTick RVR follows CSR by 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SYSTICK_RVR - SYSTICK_CSR).to_equal(4)
```

</details>

#### ARM SysTick CVR follows RVR by 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SYSTICK_CVR - SYSTICK_RVR).to_equal(4)
```

</details>

#### RISC-V CLINT base is 0x02000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CLINT_BASE).to_equal(0x02000000)
```

</details>

#### RISC-V CLINT mtimecmp offset from base is 0x4000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CLINT_MTIMECMP - CLINT_BASE).to_equal(0x4000)
```

</details>

#### x86_64 APIC base is 0xFEE00000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(APIC_BASE_ADDR).to_equal(0xFEE00000)
```

</details>

### TimerConfig

#### stores arch and tick_hz

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_timer_config(TIMER_ARCH_ARM, 1000)
expect(cfg.arch).to_equal(0)
expect(cfg.tick_hz).to_equal(1000)
expect(cfg.initialized).to_equal(true)
```

</details>

#### selects SysTick base for ARM

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timer_base_addr_for(TIMER_ARCH_ARM)).to_equal(SYSTICK_CSR)
```

</details>

#### selects CLINT base for RISC-V

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timer_base_addr_for(TIMER_ARCH_RISCV)).to_equal(CLINT_BASE)
```

</details>

#### selects APIC base for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timer_base_addr_for(TIMER_ARCH_X86_64)).to_equal(APIC_BASE_ADDR)
```

</details>

#### returns 0 for unknown arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timer_base_addr_for(99)).to_equal(0)
```

</details>

#### computes ARM reload value for 16 MHz / 1 kHz

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reload = arm_reload(16000000, 1000)
expect(reload).to_equal(15999)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
