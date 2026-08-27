# RISC-V Gen2 Accepted-Effect Fence Product

Status: development evidence; self-hosted qualification pending.

This scenario validates the mission-critical typed boundary for `FENCE` and
`FENCE.I`. Cycle behavior is covered by the companion generated-VHDL GHDL test;
neither artifact is qualification evidence until executed by an admitted full
self-hosted Simple CLI.

## Scenario 1: Hold a FENCE behind the effect boundary

1. Build the exact RV32 FENCE owner.
2. Verify the owner enters `pending` before `full` completion.
3. Verify effect acceptance is the only transition from pending effect to
   architectural completion.

## Scenario 2: Reject unsupported encodings and profiles

1. Build a reserved nonzero-`fm` FENCE encoding.
2. Verify it selects precise illegal completion instead of an effect.
3. Attempt FENCE.I under a profile without Zifencei and require rejection.

## Scenario 3: Use the sole architectural completion path

1. Compose an RV64 FENCE.I product.
2. Verify exactly one stateful fence provider and one retirement owner.
3. Verify strict VHDL contains the explicit effect handshake and common fault
   aggregator.

## Executable source

`test/03_system/app/hardware/feature/riscv_gen2_fence_owner_spec.spl`

## Behavioral evidence

`test/02_integration/compiler/riscv_scalar_fence_cycle_ghdl_spec.spl` drives
effect and completion backpressure, proves no retirement before acknowledgement,
checks single consume, and proves runtime-illegal events issue no effect.
