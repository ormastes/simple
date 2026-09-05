# RV32 QEMU Oracle Live Evidence

- contract_version: 1
- status: fail
- reason: missing-media-manifest
- lane: rv32
- runner: scripts/os/check_riscv_linux_qemu.shs
- invocation: sh scripts/os/check_riscv_linux_qemu.shs rv32
- gate_failed: media-manifest
- gate_stage: prerequisite
- qemu_launched: 0
- decisive_line: "ERROR: missing media manifest: build/os/rv32_soc/manifest.txt"
- expected_manifest: build/os/rv32_soc/manifest.txt
- expected_manifest_present: 0
- expected_initramfs: build/os/rv32_soc/initramfs.cpio.gz
- expected_initramfs_present: 0
- expected_buildroot_manifest: build/os/buildroot/rv32/buildroot-manifest.txt
- expected_buildroot_dir_present: 0
- found_initramfs: build/os/rv32_soc/initramfs_login.cpio.gz
- found_initramfs_bytes: 7928683
- found_image_bytes: 31022080
- found_fw_jump_bytes: 268968
- media_provenance: stale-pre-provenance-builder-output
- login_prompt_seen: 0
- shell_reached: 0
- ls_root_executed: 0
- transcript_origin: none
- attempts_spent: 1
- attempts_cap: 3
- deterministic_failure: 1

## Assessment

The first live run of the fixed `scripts/os/check_riscv_linux_qemu.shs rv32`
never reaches QEMU. It fails its first prerequisite gate, so no boot was
attempted and no transcript exists.

`build/os/rv32_soc/` holds `Image` and `fw_jump.bin` but no `manifest.txt`,
`build/os/buildroot/rv32/` does not exist, and the initramfs is still named
`initramfs_login.cpio.gz` — the pre-provenance builder's output name, not the
current builder's `initramfs.cpio.gz` + `manifest.txt` pair. The RV32 pinned
media are therefore stale leftovers from an older builder pass.

Consequence: the OpenSBI/`-initrd` FDT handoff fix recorded on 2026-07-24
remains **untested**. It may well be correct, but nothing has exercised it.

AC-9 and AC-10 are blocked upstream of the boot path, not on a boot bug.

The failure is deterministic (a missing file, not flakiness), so one attempt of
the three-cycle cap was spent and retries were correctly not attempted.

## Unblock path

Re-run to completion, in order:

1. `scripts/os/build_riscv_linux_assets.shs`
2. `scripts/os/build_riscv_buildroot.shs`

Buildroot alone took three bounded cycles in the prior session, so budget for a
multi-cycle task. Re-run the oracle only after both produce current
`manifest.txt` provenance.

## Traceability

- AC-5: this report records the current RV32 blocker.
- AC-9: blocked — pinned media cannot be bound to provenance.
- AC-10: blocked — no `login:`, shell, or `ls /` evidence is reachable.
