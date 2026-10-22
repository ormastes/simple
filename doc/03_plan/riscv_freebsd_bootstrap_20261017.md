# RISC-V FreeBSD bootstrap execution plan

Status: in progress; VM, Rust and admitted LLVM probes passed; Simple bootstrap pending.

## User-selected outcome

The requested target is a persistent RISC-V BSD VM with Clang, Rust and the
remaining bootstrap tools, a real bootstrap with platform failures repaired,
and reviewed fixes merged into `release_phase3`. Disk maintenance is part of
the work. These requirements come directly from the user's objective.

| Requirement | Completion evidence |
| --- | --- |
| REQ-001 Recover disk space regularly | Before/after free-space receipts and a bounded cleanup procedure that preserves active sessions and unapproved dirty work |
| REQ-002 Boot a persistent FreeBSD riscv64 VM | Checksum-verified base, persistent overlay, guest `uname -srm`, SSH access, reboot and reconnect |
| REQ-003 Supply guest build tools | Guest versions of Clang, Rust, Cargo, admitted LLVM, Git, GNU make, pkgconf, coreutils, rsync and required libraries; successful compilation and execution probes |
| REQ-004 Bootstrap on the guest | Canonical native checker succeeds with Stage 2 admission, Stage 3 provenance and an executed compiled probe |
| REQ-005 Repair RISC-V/BSD failures | Reproduced failures, scoped source changes and relevant regression evidence; no seed fallback presented as self-host proof |
| REQ-006 Land fixes | Reviewed PR containing only owned changes merged into `release_phase3` |

## Verified execution update — 2026-10-18

- Removed seven obsolete snapshot worktrees after retaining changed/untracked
  files and Git recovery references. Archives remain under
  `build/worktree-cleanup-archive/20261017/`. Physical C: free space exceeded
  100 GiB at the latest phase check. Removing unused LLVM 23.1.3 sources also
  freed approximately 2.6 GiB inside WSL; this does not imply immediate physical
  Windows VHD reclamation. Guest daily `/tmp` cleanup is now enabled through
  native `periodic`, with seven-day access/modification/change-age retention.
  Cron is running and its daily entry is present. Source, toolchain caches and
  evidence under `/root` are outside that cleanup root. The unsafe repository
  QEMU cleanup helper remains unused; reboot persistence is not yet verified.
- FreeBSD 14.4 riscv64 boots under QEMU 10.2.1 with a persistent 64 GiB overlay,
  four virtual CPUs, 6 GiB RAM and working SSH. The official base checksum and
  image integrity passed. Reboot-and-reconnect verification remains pending.
- Guest base Clang 19.1.7 and Rust/Cargo 1.98.1 compiled and executed probes.
- LLVM 23.1.2 was built on Linux as native FreeBSD RISC-V executables against
  the guest sysroot, installed in `/usr/local/llvm23`, and qualified by guest
  Clang compiling a C probe whose executable produced `42`.
  `llvm2312-qualification.log` records
  `llvm2312_guest_compile_execute_status=pass`; the deployment process exited 0.
  The toolchain archive SHA-256 is
  `c6e34c522cbe9cd23ecb4a59663f266e61158e2ff68cc91cefee1de8bec8e64f`.
- Cross-build recovery required setting CMake's module linker flags to LLD,
  in addition to executable/shared linker flags. Extraction must use
  `tar --no-same-owner` so FreeBSD's loader cache accepts root-owned libraries.
- Installed guest tools now include pkg 2.8.4, GNU Make 4.4.1, Python 3.13.16,
  rsync 3.5.1 and CMake/CTest/CPack 3.31.12. Rsync passed a checksum/archive
  transfer comparison. CMake passed native C/C++ configuration with Clang
  23.1.2, compilation and execution of a probe producing `42`, before install.
  Its cross-built archive SHA-256 is
  `dfcc7d10b6223a376d71b29ac942d6dd84248536924a68fec0dc6403410ad775`.
  The slower native CMake build was stopped only after qualification; its
  cache and the completed GNU Make/Python installations were preserved.
- Perl's Encode extension invoked BSD `make` with GNU jobserver flags. A
  native isolated fixture reproduced that failure and passed with explicit
  `MAKE=/usr/local/bin/gmake`. After the original Unicode generator completed,
  the repair resumed the cached Perl build using that override. Full Perl
  installation and libcurl/Git/coreutils/pkgconf/libffi/zstd remain pending;
  no complete-toolset or Simple bootstrap PASS is claimed.
- PRs #3638 and #3640 merged host/target alignment fixes into `release_phase3`.
  The staged guest source is pinned to
  `070b8181df63f137b7cedd2dd2ab1099db25a375`; actual Git identity validation
  waits for guest Git installation. The canonical native checker is queued
  behind dependencies. No Simple Stage 2/3 bootstrap PASS is claimed.

Live handles and run-specific logs are recorded locally in
`build/riscv-freebsd/active-run-state.json`. Preserve completed checks and build
caches; inspect terminal results before resuming a failed stage.

## Initial evidence — 2026-10-17

Inspection on 2026-10-17 found Windows C: below 2 GiB free. The Ubuntu WSL
filesystem reports hundreds of GiB logically available, but its backing file
still consumes the Windows volume; that figure does not establish physical
capacity for a VM or compiler build. The wrapper's existing floor is 30 GiB.

Twenty registered worktrees have creation and root modification timestamps
older than seven days. Every candidate contains dirty or ignored contents.
Discard authorization is pending; none was removed. Branches and commits must
remain when an authorized worktree is removed. Do not infer inactivity from
timestamps alone or recursively delete through reparse points.

Ubuntu WSL provides QEMU 10.2.1, Clang 21.1.8, qemu-img, rsync, xorriso,
OpenSBI `fw_dynamic.bin` and RISC-V S-mode U-Boot. Its `rustc` is a rustup shim
with no default toolchain and fails. These are host observations, not evidence
of guest tools. WSL reports 15 GiB RAM, so the wrapper's 32G RAM default is
unsuitable for this host.

The branch wrapper accepts only amd64 and arm64. It assumes a BASIC-CLOUDINIT
image and includes an x86_64 Stage 3 path and Cranelift checks. Adding an
architecture spelling alone cannot satisfy REQ-002 or REQ-004.

Official candidate media:
<https://download.freebsd.org/releases/VM-IMAGES/14.4-RELEASE/riscv64/Latest/>
lists `FreeBSD-14.4-RELEASE-riscv-riscv64-ufs.qcow2.xz`. Availability of this
ordinary VM image does not prove cloud-init provisioning support. Obtain and
validate the official checksum before admitting any downloaded image.

## Execution and failure boundaries

1. Resolve dirty-worktree cleanup, then remeasure physical Windows free space.
   Never start the download/build by lowering the existing disk floor.
2. Use the isolated branch `work/riscv-freebsd-bootstrap-20261017`, based on
   `release_phase3`. The sparse worktree excludes unrelated concurrent edits.
3. Verify RISC-V guest provisioning against the actual image: OpenSBI,
   U-Boot, virtio storage/network, console and SSH. Establish a persistent
   image lifecycle separate from disposable checker overlays. Never modify
   an admitted base image in place.
4. Install and execute guest tool probes. Confirm the admitted LLVM provider
   is available for riscv64 before launching the expensive bootstrap. Record
   missing binary packages explicitly; do not silently substitute LLVM 18
   for a checker requiring LLVM 23.
5. Derive the native target triple from admitted target metadata. Remove
   x86-specific result paths and unsupported backend assumptions from the
   RISC-V route while preserving existing target behavior.
6. Run the canonical native-FreeBSD checker and retain its own logs and
   receipts. Repair the first independent failure; retain useful caches.
   Limit each feature to three verification/fix cycles and never repeat a
   passing acceptance check without a relevant source change.
7. Review negative cases: missing firmware, invalid image checksum, absent
   provisioning support, wrong guest architecture, missing LLVM/Rust,
   insufficient physical disk space, and stale/mismatched bootstrap receipt.
   All must fail before a misleading PASS or destructive cleanup.
8. Verify source and documentation changes, review the exact PR head and
   comments, and merge only this lane into `release_phase3`. No release tags
   or publication are authorized.

## Ownership

Implementation, merge ownership and final review: this Codex session.
Sidecar lanes: N/A. No unrelated dirty files are included. No recurring
background deletion job is installed; disk checks occur at phase boundaries
until a safe retention procedure is implemented and verified.
