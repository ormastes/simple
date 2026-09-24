# aarch64 in-guest clang compile — lane status & blocker record

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (scripts/qemu/check_simpleos_arm64_clang_compile.shs)
Host: aarch64 Linux, KVM, 20 cores. NO x86 guests used (host rule honored).

## Rung status

| Rung | Status | Evidence |
|---|---|---|
| R1 image staged + host-verified | **PASS** | `image_verify OK entries=['CLANGELF','CRT0O','HELLOC','LIBCA','LLDELF','SIMPLEOSLD']`, image 180,987,904 B at `build/os/elfexec_clang_arm64/fat32-clang-arm64.img`; writer status `fsexec_mkimg_clang_arm64_status=ok root_entries=6` |
| R2 guest boots | BLOCKED | kernel cannot link (below) — 0 boot cycles consumed |
| R3 clang --version in guest | BLOCKED (needs R2) | — |
| R4 in-guest compile+link | BLOCKED (needs R2) | — |
| R5 in-guest run | BLOCKED (needs R2) | — |

## Blocker (pre-existing on main, not caused by this lane)

The arm64 fs-exec kernel closure fails to link on current main
(`codex/spipe-local-knowledge-setup` @ 6d9fcc89f5d + parents) for ANY entry,
including the stock `fs_exec_entry.spl`. Three independent missing pieces,
all in files owned by other lanes (not modified here per lane rules):

1. `fn app_registry_leaf_for_canonical` — referenced (never defined) at:
   - `src/os/services/vfs/direct_fat32_boot_reader.spl:829`
   - imported by `src/os/services/vfs/vfs_boot_state.spl:6`
   - also referenced from `nvme_filesystem_direct_io.spl`, `nvme_boot_runtime_owner.spl`, `nvme_q35_lease_perf.spl`
   Linker: "reached the linker undeclared … referenced at direct_fat32_boot_reader.spl:772/829".
2. `fn _arm_fs_error_is_not_found` — used at `src/os/services/vfs/arm_fs_exec_vfs.spl:823`, defined nowhere in the tree (`git grep "fn _arm_fs_error_is_not_found" HEAD` → empty).
3. `fs_exec_entry.spl` itself references an undefined `sim_rc` in `spl_start` (the `[simple-gate] execution:fail … rc={sim_rc}` branch) and fails codegen under `SIMPLE_NO_STUB_FALLBACK=1` before the linker stage is even reached.

Resume command once the owning lanes land the two `fn` definitions (+ the
`sim_rc` fix or use of the custom entry):

```
sh scripts/qemu/check_simpleos_arm64_clang_compile.shs
```

The custom entry `examples/09_embedded/simple_os/arch/arm64/clang_bringup_entry.spl`
(commit f828787 area) sequences R3-R5 via blocking `arm64_fs_exec_spawn_ring3`
and is clean of issue (3); the remaining block is the VFS closure (issues 1-2).

## Landed this lane (committed)

- `examples/09_embedded/simple_os/arch/arm64/clang_bringup_entry.spl` — R3-R5 rung entry.
- `scripts/os/fsexec_mkimg_clang_arm64.spl` — FAT32 root-only 8.3 stager
  (CLANG.ELF + LLD.ELF big payloads; CRT0.O/SIMPLEOS.LD/LIBC.A/HELLO.C smalls).
  **Seed divergence fixed**: the seed interpreter's `text.length` yields a bool;
  the stager uses `.len()` (the lld sibling stager has the same latent issue
  under the seed — left untouched, other lane's file).
- `scripts/qemu/check_simpleos_arm64_clang_compile.shs` — R1 host-verified
  staging + kernel build + KVM boot + serial rung gates.

## Toolchain inputs (lane-C1 aarch64, unchanged)

- Guest clang/lld: `/home/yoon/llvm-project-simpleos/build-os-llvm/cross-aarch64-unknown-simpleos/bin/`
- Sysroot: `/home/yoon/llvm-project-simpleos/build-os-llvm/sysroot-aarch64/`
