# RISC-V QEMU Heap Policy Contract

The static contract pins the QEMU virt no-allocation heap window to immutable
Pure Simple scalars: start `0x87000000`, size `16777216` bytes. Five boot
consumers import those values directly. Neither a C provider nor a raw-runtime
declaration remains.

Source: `test/01_unit/os/kernel/boot/riscv_qemu_heap_policy_contract_spec.spl`

Evidence class: static source contract. It does not prove live allocation or
boot behavior on QEMU or physical RISC-V hardware.

## Purpose and audience

This manual is for SimpleOS HAL maintainers reviewing foreign-policy removal.
It makes constant ownership, consumer routing, provider deletion, and inventory
cleanup independently auditable.

## Scorecard

| Scenarios | Active | Skipped | Pending |
|-----------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

| Static obligation | Expected result |
|-------------------|-----------------|
| Pure Simple owner | Exact public `u64` start and size scalars |
| Consumer routing | Five boot files use direct scalar imports |
| Runtime isolation | No migrated consumer uses either raw symbol |
| C provider removal | Neither former C function remains |
| Inventory cleanup | Six raw-SFFI rows and two unbacked entries absent |

## Operator workflow

Run:

```text
bin/simple test test/01_unit/os/kernel/boot/riscv_qemu_heap_policy_contract_spec.spl
```

A pass establishes only the static obligations above. Use the RISC-V QEMU boot
gate separately for behavioral evidence.

## Performance and coverage properties

Both exported policies are immutable scalars. Consumer access is O(1), requires
zero allocation, performs no copy, and introduces no function dispatch. The
policy surface contains no decisions, so its branch and condition set is empty;
the two exact-value assertions completely cover its observable results.

## Compatibility and limitations

The values and call-site order are unchanged. The parser regression fixture at
`test/01_unit/compiler/parser/rv64_boot_call_parser_spec.spl` intentionally
retains its synthetic nested raw-call text because it covers grammar rather
than production runtime ownership. This contract does not claim generated-code
inlining, timing measurements, or hardware execution evidence.
