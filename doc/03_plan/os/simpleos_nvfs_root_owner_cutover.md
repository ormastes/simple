# SimpleOS NVFS root owner cutover plan

Architecture: `doc/04_architecture/os/storage/simpleos_nvfs_root_owner_cutover.md`.
Requirements: `doc/02_requirements/feature/simple_platform_unification.md`
REQ-008..010, REQ-012, REQ-017..018. The current FAT32 and copied-IPC paths
are implementation inputs, not NVFS release evidence.

## Ordered implementation

1. **Production FD join.** Derive `FdTaskLifecycleKeyV1` from the scheduler's
   current lifecycle identity. Create the descriptor context at task admission
   and bind syscall 30 to `positioned_fd_open_existing_v1` only for an admitted
   MountTable root. Use the existing rollback receipt. Keep O_CREAT/O_TRUNC and
   append explicitly unavailable until owned mutations are implemented.
2. **Whole FD lifecycle.** Route 31/32/33, lseek, fstat, sync, dup/dup2/fork,
   exec, exit/reap cleanup, and positioned 134/135 through the same OFD owner.
   Handle copyout failure without advancing the shared cursor; quarantine
   committed-unknown close rather than reusing the number. Remove the
   `FD_TYPE_FAT32` fallback from the release profile only after parity.
3. **Catalogue bridge.** Review and implement one bounded private service-to-
   MountTable request boundary. Authenticate the scheduler caller against the
   exact current catalogue VFS service generation, validate method/length and
   file authority, and retain the root binding until reply retirement. The
   service must not call public file syscalls or open a second NVMe filesystem.
4. **Boot and image binding.** Bind the root's lease, mount generation, and
   image identity into service admission and PID1 readiness. Production
   catalogue startup rejects private FAT32. Restart rebinds the same root;
   failed rebind leaves the endpoint unready. Development FAT32 remains
   explicitly labeled and cannot satisfy release evidence.
5. **Guest qualification.** Build one immutable NVFS image with an admitted
   self-hosted runtime. Cold boot it, open/write/read/close through both
   public file syscalls and the catalogue IPC route, restart `vfs`, verify
   one root generation, reboot the derived writable state, and read the
   exact marker. Retain candidate/derived-state hashes, serial logs, syscall
   receipts, mount facts, and persistence evidence.

## Negative and failure matrix

Reject wrong task/lifecycle generation, stale FD, wrong service generation,
invalid buffer or frame length, absent NVFS root, second writable mount,
unadmitted FAT32 fallback, unsupported mutating open, failed copyout, service
crash after dispatch, close ambiguity, and changed candidate bytes. None may
produce a release PASS or reuse a live/uncertain descriptor number.

## Handoff and review

Sidecar lanes: N/A for the authority and ABI design; focused source inventories
may be delegated only after the interface and fail-fast test helpers are fixed.
Merge owner: SimpleOS VFS/kernel file owner. Final reviewer: independent
normal/highest-capability reviewer. No release promotion before `/verify`
reports PASS for the exact immutable candidate.
