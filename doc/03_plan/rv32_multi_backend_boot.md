<!-- codex-design -->
# RV32 Multi-Backend Boot — Plan

**Date:** 2026-04-02
**Status:** Draft
**Requirement:** [rv32_multi_backend_boot](../02_requirements/feature/rv32_multi_backend_boot.md)

## Objective

Align the repo narrative around one RV32 proof matrix:

- QEMU proves OS boot.
- GHDL proves remote RV32 payload execution.
- `examples/mllvm_qemu_rtl` proves timing and RTL simulation, but not OS boot yet.

## Workstreams

### W1: QEMU boot proof

- Keep the existing `src/os/kernel/arch/riscv32` boot path and its smoke test as the authoritative OS boot lane.
- Add docs and a test matrix entry that names the artifact and the boot status explicitly.

### W2: GHDL remote lane

- Keep the existing RV32 composite runner and GHDL adapter scoped to payload execution.
- Make the documentation say payload execution unless a real boot contract is added later.

### W3: Hybrid/RTL lane

- Keep the hybrid simulator scoped to model-level execution.
- If future work wants OS boot here, it must add real image loading and board/boot support first.

## Recommended Delivery Order

1. Publish the research and requirements docs.
2. Add the architecture and design docs that define the proof matrix.
3. Add the test plan that records the existing passing lanes and their exact scope.
4. Keep implementation work separate from the docs slice.

## Risks

- Overstating the hybrid/RTL lane as an OS boot proof would make the documentation false.
- Treating the GHDL remote lane as a boot lane would blur the existing remote execution contract.
- Leaving the artifact name implicit would make future test claims hard to verify.

