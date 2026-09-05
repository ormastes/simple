# SimpleOS three-architecture QEMU execution evidence

Status: **BLOCKED — structural admission implemented; no live run authorized in this session.**

The canonical adapter is
`scripts/check/check-simpleos-three-arch-qemu-bundle.shs`. It consumes SOSIX
bundle records and requires hash-bound retained compiler, kernel, image,
mounted program, firmware, argv, marker, and transcript artifacts. It validates
x86_64 SysV, AArch64 AAPCS64, and RV64GC LP64D ELF identities and rejects Rust
seed, stale/source-mismatched, symlinked, direct-loader, `-kernel`, opaque
firmware, fallback, reordered-marker, and missing-receipt evidence.

Final-review authority blocker: evidence records, argv, hashes, status, and
serial markers are caller-authored bytes, while `! -L` followed by a separate
path hash has a TOCTOU window. No canonical signed campaign verifier and no
descriptor-bound no-follow identity/hash owner currently exist. Consequently
the adapter reports record structure only as `valid-untrusted`, then returns
`BLOCKED`/nonzero for every live `--check`. It cannot emit a live PASS until
both owners land and the self-tests prove forged status/log campaigns remain
rejected.

| Row | Current blocker | Exact resume command | Required retained result |
|---|---|---|---|
| x86_64 QEMU | Current fs-exec lane uses `-device loader`; no same-run OVMF, Stage-4 compiler, mounted-program, and immutable profile bundle | `SIMPLE_BIN=/absolute/admitted/stage4/simple BUILD_DIR=build/simpleos_wm_fullscreen_evidence sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs` then `sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check x86_64 BUNDLE_DIR` | OVMF bytes/hash/version; exact argv; compiler admission/binary; kernel/image/program; ordered serial; receipt |
| AArch64 QEMU | Existing fs-exec spec uses `-kernel`; real AAVMF gate does not yet execute the mounted filesystem program or retain the complete bundle | `AAVMF_CODE=/absolute/AAVMF_CODE.fd AAVMF_VARS=/absolute/AAVMF_VARS.fd sh scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs` then run the admitted mounted-program producer and `sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check arm64 BUNDLE_DIR` | AAVMF code/vars hashes/version; BOOTAA64 path; Stage-4 compiler; AArch64 kernel/program ABI; image; ordered transcript |
| RV64GC QEMU | Current descriptor uses `-bios default`; the real-firmware probe boots OpenSBI alone and does not prove SimpleOS mounted-program execution | `OPENSBI_FW_DYNAMIC=/absolute/fw_dynamic.bin sh scripts/check/check-simpleos-riscv64-opensbi-real-firmware-boot.shs` then run the admitted mounted-program producer with that exact firmware and `sh scripts/check/check-simpleos-three-arch-qemu-bundle.shs --check riscv64 BUNDLE_DIR` | OpenSBI bytes/hash/version; RV64GC LP64D kernel/program; Stage-4 compiler; image; ordered transcript; receipt |

Source/static checks cannot promote these rows. Run each hardware-dependent
command only after the active bootstrap/build owner releases its caches.

The executable source-contract spec and its operator manual are present. Run
the following only after the admitted Stage-4 runtime is available; this
session intentionally did not execute a runtime or regenerate the manual while
the bootstrap owner was active:

```sh
bin/simple test test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl --mode=interpreter
bin/simple sspec-maintain scan test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl
bin/simple spipe-docgen test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl --output doc/06_spec --no-index
```

Residual maintainability blocker: the concurrently modified canonical target
catalog, `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl`,
is 987 lines. This evidence lane did not edit or split that other-owner file.
