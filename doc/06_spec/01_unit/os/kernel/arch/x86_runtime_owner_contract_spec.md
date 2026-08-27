# x86 VMM D4 Source and Interrupt-Leaf Dedup Contract

> x86_64 paging implements the VMM D4 Step 6 source delegation, while the
> migrated x86_32 interrupt leaf reaches LIDT through its package-visible typed
> owner without a private raw-runtime declaration or call.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

Source: `test/01_unit/os/kernel/arch/x86_runtime_owner_contract_spec.spl`

Evidence class: `source-contract`.

## Purpose and audience

This manual lets SimpleOS HAL maintainers review the x86_64 VMM D4 Step 6 source
implementation and the migrated x86_32 LIDT leaf boundary without executing
privileged instructions on the host.

## Operator workflow

Run `bin/simple test test/01_unit/os/kernel/arch/x86_runtime_owner_contract_spec.spl`.
All three scenarios must pass before accepting an x86 HAL runtime-owner move.

## Compatibility and limitations

The x86_64 scenario structurally pins the VMM D4 Step 6 source implementation;
it does not prove live behavior, and G-spec/G-ovmf verification remains pending.
The checks do not claim global single runtime ownership and do not replace the
x86 architecture boot or QEMU behavior gates.

## Scenarios

### x86 VMM D4 source and migrated interrupt-leaf dedup

#### pins x86_64 VMM D4 Step 6 source delegation through the test-aware core owner

- Read the x86_64 paging leaf and VMM core owner.
- Require `_load_cr3` through the existing `vmm_core` import and use it from
  `vmm_switch_address_space`.
- Reject every paging-to-CPU import and dead CR3-read helper.
- Reject `rt_read_cr3` / `rt_write_cr3` in the paging leaf.
- Confirm package-visible `_load_cr3` retains the hosted test fallback before
  its raw hardware call.

<details>
<summary>Executable SSpec</summary>

```simple
val paging = file_read_text(X86_64_PAGING_PATH)
val core = file_read_text(VMM_CORE_PATH)
expect(paging).to_contain("use os.kernel.memory.vmm_core.{vmm_publish_kernel_pml4, _load_cr3}")
expect(paging).to_contain("fn vmm_switch_address_space(pml4_phys: u64):")
expect(paging).to_contain("    _load_cr3(pml4_phys)")
expect(paging.contains("use os.kernel.arch.x86_64.cpu")).to_be(false)
expect(paging.contains("read_cr3")).to_be(false)
expect(paging.contains("rt_read_cr3(")).to_be(false)
expect(paging.contains("rt_write_cr3(")).to_be(false)
expect(core).to_contain("pub(package) fn _load_cr3(pml4_phys: u64):")
expect(core).to_contain("if mmio_test_mode_enabled():")
expect(core).to_contain("_vmm_fallback_cr3 = pml4_phys")
expect(core).to_contain("rt_write_cr3_raw(pml4_phys)")
```

</details>

#### routes x86_32 IDT loading through the canonical CPU owner

- Read the x86_32 interrupt leaf and CPU owner.
- Require the `lidt` CPU import and call.
- Reject `rt_lidt` in the interrupt leaf.
- Confirm its raw declaration remains behind package-visible `lidt` in
  `x86_32/cpu.spl`.

<details>
<summary>Executable SSpec</summary>

```simple
val interrupt = file_read_text(X86_32_INTERRUPT_PATH)
val cpu = file_read_text(X86_32_CPU_PATH)
expect(interrupt).to_contain("use os.kernel.arch.x86_32.cpu.{port_outb, port_outb_wait, port_inb, cli, sti, lidt}")
expect(interrupt).to_contain("lidt(&g_idtr as u32)")
expect(interrupt.contains("rt_lidt(")).to_be(false)
expect(cpu).to_contain("extern fn rt_lidt(idtr_addr: u32)")
expect(cpu).to_contain("pub(package) fn lidt(idtr_addr: u32):")
```

</details>

#### removes migrated leaf rows from the unsafe baseline

- Reject the three migrated-leaf rows named by the executable assertions.

<details>
<summary>Executable SSpec</summary>

```simple
val baseline = file_read_text(RAW_SFFI_BASELINE_PATH)
expect(baseline.contains("src/os/kernel/arch/x86_64/paging.spl\trt_read_cr3\t")).to_be(false)
expect(baseline.contains("src/os/kernel/arch/x86_64/paging.spl\trt_write_cr3\t")).to_be(false)
expect(baseline.contains("src/os/kernel/arch/x86_32/interrupt.spl\trt_lidt\t")).to_be(false)
```

</details>
