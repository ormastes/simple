# SimpleOS Purity and Duplication Audit (2026-05-05)

## Scope

Objective slice audited: make SimpleOS more pure Simple and remove duplication while preserving the QEMU evidence for filesystem boot, SSH, WM, and browser lanes.

Owned-code scope excludes vendored/runtime third-party files per `AGENTS.md`.

## Findings

### File Size

Top oversized SimpleOS-owned files measured on 2026-05-05 with
`find src/os examples/simple_os -name '*.spl' -not -path '*/vendor/*' ... | wc -l`:

| File | Lines | Finding |
|---|---:|---|
| `src/os/kernel/ipc/syscall.spl` | 3740 | Exceeds 800-line refactor target; dispatcher mixes syscall routing, user-copy helpers, wait/task info, datasets, queues, DMA, SPM, and privilege handling. |
| `examples/simple_os/arch/x86_64/wm_entry.spl` | 3603 | Exceeds 800-line target; likely test-entry fixture with repeated GUI setup patterns. |
| `src/os/qemu_runner.spl` | 2945 | Exceeds 800-line target; scenario catalog, media setup, command construction, and result parsing are still coupled even after desktop/toolchain/SSH contract extraction. |
| `src/os/kernel/scheduler/scheduler.spl` | 2710 | Exceeds 800-line target; scheduler core and accessor surface are in one module. |
| `src/os/services/vfs/vfs_init.spl` | 1835 | Exceeds 800-line target; VFS init, seeded executable materialization, FAT32 fallbacks, cache handling, and alias normalization remain concentrated. |
| `src/os/kernel/abi/syscall_shim.spl` | 1795 | Exceeds 800-line target; ABI shim surface remains broad. |
| `src/os/kernel/memory/vmm.spl` | 1753 | Exceeds 800-line target; VMM mapping, copy helpers, status types, and page-table walk logic are combined. |
| `src/os/tls13/tls13.spl` | 1742 | Exceeds 800-line target; TLS protocol logic remains broad. |
| `src/os/crypto/p384.spl` | 1653 | Exceeds 800-line target; crypto implementation size is high but not yet audited for duplication. |
| `src/os/crypto/snow3g.spl` | 1574 | Exceeds 800-line target; crypto implementation size is high but not yet audited for duplication. |
| `src/os/tls13/handshake13.spl` | 1487 | Exceeds 800-line target; TLS handshake logic remains broad. |
| `src/os/services/launcher/launcher.spl` | 1452 | Exceeds 800-line target; registry, process tracking, command resolution, and launch are combined even after seeded metadata consolidation. |

### Duplicate Checker Status

Attempted token duplicate scans on 2026-05-05:

- `bin/simple duplicate-check src/os --mode token --min-lines 5`
- `bin/simple duplicate-check src/os/services/launcher --mode token --min-lines 5`
- `bin/simple duplicate-check src/os/kernel --mode token --min-lines 5`

All three current runs were wrapped in `timeout 30s`; each printed only its
scan count and exited `124`:

- `src/os`: `Scanning 594 files...`, timed out.
- `src/os/services/launcher`: `Scanning 1 files...`, timed out.
- `src/os/kernel`: `Scanning 204 files...`, timed out.

This is not sufficient evidence that duplication is absent. The duplicate
checker itself remains a blocker for broad duplicate-clearance proof.

### Concrete Cleanup Performed

`src/os/qemu_runner.spl` had repeated string literals for `build/os/x64-desktop-disk.serial.log` after the x64 desktop disk harness fix. This was replaced by `desktop_disk_serial_log_path()`, matching the existing UEFI and WM serial-log helper pattern.

`src/os/services/vfs/vfs_init.spl` had repeated C FAT32 executable seed blocks for hello, clang, rust, and simple app images. These now share `_seed_c_fat32_exec_bytes(label, path)`, which delegates to the existing C FAT32 read/ELF validation helper and keeps boot-log evidence consistent across seeded apps.

Additional current cleanup evidence:

- `src/os/services/vfs/vfs_init.spl` centralizes lazy executable-cache path equivalence in `_vfs_lazy_exec_id()`.
- `src/os/services/vfs/vfs_init.spl` centralizes common disk/root executable alias leaves in `_vfs_common_exec_disk_leaf()`.
- Browser/hello seeded fallback now reuses `_seeded_exec_leaf_for_path()`.
- Mounted/direct executable candidate reads now share `_vfs_read_mounted_exec_candidate()` and `_vfs_read_direct_exec_candidate()`.
- `src/os/services/launcher/launcher.spl` derives seeded app name/icon/key metadata from the canonical seeded app index instead of repeating app aliases in separate tables.
- `src/os/desktop_qemu_contract.spl`, `src/os/toolchain_vfs_probe_contract.spl`, and `src/os/ssh_qemu_contract.spl` own desktop/toolchain/SSH QEMU acceptance contracts that were previously concentrated in `src/os/qemu_runner.spl`.
- Shared desktop toolchain marker groups are composed through `desktop_toolchain_*_marker_fragments()` helpers instead of duplicated across disk and UEFI contracts.

## Prompt-to-Artifact Checklist

| Requirement | Artifact or command checked | Evidence summary | Covered? |
|---|---|---|---|
| Make SimpleOS more pure Simple | `src/os/services/vfs/vfs_init.spl`; `src/os/services/launcher/launcher.spl`; extracted QEMU contract modules | Several repeated alias, seeded metadata, executable read, and QEMU contract surfaces now route through shared Simple modules/helpers. | Partial: large mixed-responsibility modules remain. |
| Remove duplication | `rg` for new helper symbols; focused source inspection; duplicate-check runs | Concrete local duplication was removed in VFS, launcher, serial-log helper, and desktop marker contracts. | Partial: broad duplicate checker proof is blocked by timeouts. |
| Preserve filesystem boot evidence | `bin/simple check src/os/qemu_runner.spl`; `bin/simple check src/os/desktop_qemu_contract.spl`; `bin/simple check src/os/toolchain_vfs_probe_contract.spl`; `test/unit/os/qemu_runner_spec.spl` | Static checks passed for runner and extracted contracts; qemu runner unit spec passed 52 examples from cache. | Covered for contract/static/unit scope; QEMU rerun evidence is recorded in the real-OS audit. |
| Preserve SSH evidence | `bin/simple check src/os/ssh_qemu_contract.spl`; `test/unit/os/qemu_runner_spec.spl`; real-OS audit SSH checklist | SSH contract module static check passed; qemu runner spec passed 52 examples; real-OS audit records live TCP success, bad-auth, and bad-session probes. | Covered for bounded probe scope, not full RFC SSH. |
| Preserve WM/browser evidence | `src/os/desktop_qemu_contract.spl`; `test/unit/os/qemu_runner_spec.spl`; real-OS audit WM/browser checklist | Desktop contract static check passed; runner spec passed; real-OS audit records WM render and browser pixel smoke evidence. | Covered for smoke scope, not full browser conformance. |

## Verification Evidence

Fresh verification run for this audit:

- `bin/simple check src/os/qemu_runner.spl` passed.
- `bin/simple check src/os/desktop_qemu_contract.spl` passed.
- `bin/simple check src/os/toolchain_vfs_probe_contract.spl` passed.
- `bin/simple check src/os/ssh_qemu_contract.spl` passed.
- `bin/simple test test/unit/os/qemu_runner_spec.spl` passed: 52 examples, 0 failed, cached unchanged.
- `bin/simple test test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl` passed: 5 examples, 0 failed, cached unchanged.
- `bin/simple test test/unit/os/services/launcher/launcher_seeded_metadata_spec.spl` passed: 2 examples, 0 failed, cached unchanged.

## Remaining Refactor Work

1. Split `src/os/kernel/ipc/syscall.spl` by syscall domains before claiming the dispatcher is pure or maintainable.
2. Continue splitting `src/os/qemu_runner.spl` into scenario catalog, media preparation, command assembly, and result parsing modules. The desktop/toolchain/SSH contracts are extracted, but the runner is still 2945 lines.
3. Fix or constrain `bin/simple duplicate-check` so it returns bounded output for owned OS subsets, then rerun semantic, token, and cosine modes.
4. Audit repeated x86_64 GUI/bootstrap setup across `examples/simple_os/arch/x86_64/*_entry.spl`.
5. Split `src/os/services/vfs/vfs_init.spl` after locking VFS seeded-app and FAT32 fallback behavior with focused regression tests.

## Status

Audit complete; implementation status remains partial. There is concrete cleanup
evidence, current oversized-file evidence, focused static/unit verification, and
an explicit duplicate-check blocker. The broader "remove duplication" requirement
is not complete until the large modules are split and a bounded duplicate scan
can prove the remaining surface.
