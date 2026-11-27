# Bare-metal RISC-V objects are base ISA only; rv64gc gets lp64, not lp64d (2026-11-16)

- id: `baremetal_riscv_target_contract_not_applied_2026_11_16`
- severity: P2
- status: open

## Symptom

`simple-p2 native-build main.spl --target riscv64gc-unknown-none-elf --emit-object`
(WSL Ubuntu-24.04, `~/xc/simple-p2`) emits an object with ELF `Flags: 0x0` and
`Tag_RISCV_arch = rv64i2p1`: no M/A/C/F/D and soft-float `lp64`. Linking it with
an `rv64gc`/`lp64d` crt0 fails in `ld.lld`:
`cannot link object files with different floating-point ABI`.
`riscv32imac-unknown-none-elf` likewise yields `rv32i2p1` (it links only because
`ilp32` matches).

Setting `SIMPLE_NATIVE_BUILD_TARGET=riscv64gc-unknown-none-elf`, the env that
`llvm_riscv64_hard_float_requested()` (`src/compiler/70.backend/backend/llvm_target.spl:52`)
reads, does not change the result. So the `RiscvTargetContract` features/ABI
(`for_target_with_mode`, `case Riscv64`/`Riscv32`) do not reach the codegen
that produces this object.

Same family as the Linux rv64 hello failure recorded in
`doc/07_guide/infra/toolchain/cross_compile_status_2026-11-15.md` (Gaps).

## Repro

```sh
OUT_DIR=/tmp/nvxc_out SIMPLE_BIN=~/xc/simple-p2 \
  sh examples/09_embedded/simpleos_nvme_fw/fw_xc/build.shs riscv64
llvm-readelf -h -A /tmp/nvxc_out/riscv64/main.o   # Flags 0x0, arch rv64i2p1
sh scripts/check/check-nvme-fw-xc-elf.shs --dir /tmp/nvxc_out   # riscv64: flags 0x1 != 0x5
```

## Same root on ARM M-profile

With `--target thumbv7em-none-eabihf` alone, the object is ARMv7-A
(`Tag_CPU_arch_profile = Application`) in ARM state. `__simple_main` has an
even `st_value`, so ld.lld turns the crt0 `bl` into `blx`, and the Cortex-M
(QEMU mps2-an386) HardFaults with an empty serial log. Exporting
`SIMPLE_NATIVE_BUILD_TARGET=thumbv7em-none-eabihf` (bug `native_build_target_flag_not_propagated_to_env_target_2026_11_16`) restores the M-profile/Thumb
object, which then boots PASS. So the `--target` triple is not propagated to the
env-keyed target selection on this native-build path.
`check-nvme-fw-xc-elf.shs` now requires a Thumb `__simple_main` for this target.

## Workaround (tagged)

`fw_xc/build.shs` assembles the rv64 crt0 with `-mabi=lp64` so the image links
and boots; `check-nvme-fw-xc-elf.shs` keeps `lp64d` (0x5) pinned, so rv64 stays
RED until codegen applies the contract.

## Fix needed

Map the `--target` triple's ISA string (`rv64gc` / `rv32imac`) to the llc
`-mattr` and `-target-abi` for bare-metal emission, then remove the workaround.
