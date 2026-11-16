# native-build `--target` is not propagated to `SIMPLE_NATIVE_BUILD_TARGET` (2026-11-16)

- id: `native_build_target_flag_not_propagated_to_env_target_2026_11_16`
- severity: P2
- status: open

## Symptom

`simple-p2 native-build main.spl --target thumbv7em-none-eabihf --emit-object`
(WSL Ubuntu-24.04, `~/xc/simple-p2` built 2026-11-16 07:12) emits an ARMv7-A
(`Tag_CPU_arch_profile = Application`), ARM-state object: `__simple_main` has an
even `st_value`. ld.lld turns the Thumb crt0's `bl` into `blx`, and the Cortex-M
(QEMU mps2-an386) HardFaults with an empty serial log.

Running the same command with `SIMPLE_NATIVE_BUILD_TARGET=thumbv7em-none-eabihf`
in the environment yields an M-profile Thumb object, which boots and prints
`SimpleOS NVMe FW PASS`. So target selection reads the env
(`app/cli/bootstrap_focused_native_build.spl:115` sets it only on that path),
and the plain `--target` path never sets it.

## Repro

```sh
SIMPLE_BIN=~/xc/simple-p2 OUT_DIR=/tmp/o sh examples/09_embedded/simpleos_nvme_fw/fw_xc/build.shs thumbv7em
sh scripts/check/check-nvme-fw-xc-elf.shs --dir /tmp/o   # RED without the env: "__simple_main is not Thumb"
```

## Workaround (tagged TODO)

`fw_xc/build.shs` exports `SIMPLE_NATIVE_BUILD_TARGET="$triple"`. Remove it once
native-build sets the env (or the target config) from `--target` on every path.

Related: `baremetal_riscv_target_contract_not_applied_2026_11_16` (on RISC-V the
env does not help; objects stay base `rv32i`/`rv64i`).
