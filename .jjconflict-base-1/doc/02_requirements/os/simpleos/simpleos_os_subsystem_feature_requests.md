# SimpleOS OS Subsystem Feature Requests

## Purpose

These feature requests turn the missing-subsystems report into implementable
work items. The target is host-OS-style application behavior: apps are loaded
from files, run as scheduler-owned processes, and use OS APIs. Drivers may keep
baremetal hardware assumptions.

New FS-exec/SSH/clang track: FR-SOS-020..050 (see below).

References:

- `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md`
- `doc/03_plan/agent_tasks/simpleos_process_apps_plan.md`

## FR-SOS-001: File I/O for Executable Loading

**Goal:** Load executable bytes from mounted filesystems through VFS.

**Requirements:**

- `g_vfs_read_file_bytes(path)` returns stable Simple-owned bytes for seeded
  app executables.
- Canonical app paths such as `/sys/apps/browser_demo` resolve to the current
  FAT32 image aliases without exposing alias names to apps.
- File reads must return enough bytes for ELF program-header validation and
  segment loading, not only the ELF magic prefix.
- Read failures return an empty byte array and emit a serial diagnostic.

**Acceptance:**

- Resolving `/sys/apps/browser_demo`, `/sys/apps/hello_world`, and
  `/sys/apps/editor` reaches real ELF bytes from FAT32.
- The loader can parse the returned bytes as ELF instead of falling back to
  resident manifest-only validation.

## FR-SOS-002: Scheduler-Owned App Tasks

**Goal:** Convert filesystem-loaded executables into scheduler-owned tasks.

**Requirements:**

- Spawn returns a scheduler PID, not a resident fallback PID.
- Launcher process records track scheduler PID, app id, state, and window count.
- Task lookup, yield, exit, wait, and reaping work for app tasks.

**Acceptance:**

- QEMU logs include `[launcher] process-backed app_id=... pid=...`.
- `launcher_find_process_by_pid(pid)` resolves the process after spawn.
- Exited app tasks are reaped without leaving stale windows.

## FR-SOS-003: Process Isolation

**Goal:** Give each app a user address space separated from kernel state.

**Requirements:**

- ELF segments map into a per-process page table.
- Kernel and MMIO regions are not writable from user code.
- User pointer validation protects syscall buffers.
- Page faults identify process, address, access type, and recovery policy.

**Acceptance:**

- A bad user pointer returns an error or terminates only the faulty process.
- One app cannot modify another app's memory or kernel memory.

## FR-SOS-004: System Memory Allocator

**Goal:** Provide robust kernel and user allocation behavior.

**Requirements:**

- Kernel heap must not be exhausted by normal desktop launch paths.
- User processes get their own heap growth API.
- `mmap`/`munmap` or equivalent supports file and anonymous mappings.
- OOM paths fail cleanly and include diagnostics.

**Acceptance:**

- Desktop launches Browser Demo, Hello World, Editor, Terminal, and File Manager
  without heap exhaustion.
- A forced oversized allocation fails without corrupting scheduler or VFS state.

## FR-SOS-005: Executable Loader

**Goal:** Load static app executables from filesystem bytes into runnable images.

**Requirements:**

- Validate ELF class, machine, program headers, segment sizes, and entry point.
- Map loadable segments with correct permissions.
- Build initial stack with path, argv, envp, and auxv placeholders.
- Reject invalid or unsupported binaries with clear errno-style results.

**Acceptance:**

- Valid seeded app ELFs build `UserProcessImage`.
- Truncated or malformed ELFs are rejected before scheduler enqueue.

## FR-SOS-006: System API and User Library

**Goal:** Give apps a stable API surface instead of baremetal calls.

**Requirements:**

- Userlib wraps syscalls for files, process lifecycle, memory, IPC, timers, and
  debug output.
- Return values use consistent errno/result mapping.
- App code does not call hardware or kernel internals directly.

**Acceptance:**

- App source can call userlib APIs and run on SimpleOS without knowing whether
  storage, graphics, or input are baremetal-backed.

## FR-SOS-007: Dynamic Library Loading

**Goal:** Support shared libraries after static app execution is reliable.

**Requirements:**

- Define shared object search paths and dependency metadata.
- Resolve symbols and apply relocations per process.
- Map shared text read-only and data privately per process.
- Surface missing-library and missing-symbol errors.

**Acceptance:**

- A dynamically linked smoke app starts with one shared library dependency.
- Static apps continue to work without the dynamic loader.

## FR-SOS-008: Syscall and Trap Return Correctness

**Goal:** Make syscall entry, dispatch, and return reliable for apps.

**Requirements:**

- Syscall 13 direct spawn must return without corrupting control flow.
- Trap handlers preserve registers required by the ABI.
- Negative errno and positive PID returns are distinguishable.

**Acceptance:**

- The QEMU desktop app path no longer emits
  `[syscall13] installed direct bridge deferred`.
- Positive PID returns reach launcher correctly.

## FR-SOS-009: Process Lifecycle

**Goal:** Complete lifecycle management for normal apps.

**Requirements:**

- Implement spawn/exec, exit, wait, kill/terminate, crash classification, and
  zombie cleanup.
- Parent/child ownership must be explicit.
- Launcher-visible state must distinguish running, exited, crashed, and
  terminated.

**Acceptance:**

- A test app exits with code 0 and the parent observes that code.
- A crashing app is marked crashed and its windows are cleaned up.

## FR-SOS-010: IPC and Window Protocol

**Goal:** Make GUI apps talk to WM/compositor through IPC.

**Requirements:**

- Apps request windows through a stable compositor IPC message.
- WM assigns ownership using scheduler PID and app id.
- Input, repaint, close, focus, and destroy events have defined message shapes.

**Acceptance:**

- Browser Demo creates its windows through IPC after process spawn.
- No app window is created by resident shell fallback.

## FR-SOS-011: App Runtime Startup

**Goal:** Provide a process entry runtime before app `main`.

**Requirements:**

- Initialize heap, stdio handles, argv/envp, panic handler, and syscall userlib.
- Preserve app path and app id.
- Define CLI vs GUI startup mode.

**Acceptance:**

- Hello World receives its app path and can print through stdio/debug output.

## FR-SOS-012: User/Kernel ABI Boundary

**Goal:** Stabilize the ABI contract between user processes and kernel.

**Requirements:**

- Define syscall register convention, pointer ownership, and buffer copy rules.
- Validate all user pointers before kernel reads or writes.
- Version ABI-visible structs and message formats.

**Acceptance:**

- Invalid syscall buffers cannot panic the kernel.
- ABI tests cover positive, negative, and boundary-sized buffers.

## FR-SOS-013: Filesystem Namespace

**Goal:** Define stable app-visible filesystem layout.

**Requirements:**

- Reserve `/bin`, `/sys/apps`, `/lib`, `/etc`, `/home`, and `/tmp`.
- Mount table lookup must hide FAT32 short-name implementation details.
- App manifests reference canonical paths only.

**Acceptance:**

- `/sys/apps/hello_world` launches regardless of root 8.3 alias details.

## FR-SOS-014: Timers and Preemption

**Goal:** Support time-based app behavior and fair scheduling.

**Requirements:**

- Provide timer interrupt or equivalent wakeup source.
- Implement sleep/timeouts for user processes.
- Prevent one app from monopolizing CPU in normal scheduling mode.

**Acceptance:**

- A sleeping app yields CPU and wakes after the requested interval.

## FR-SOS-015: Stdio, Terminal, and Pipes

**Goal:** Support normal CLI app I/O.

**Requirements:**

- Provide stdin, stdout, and stderr handles.
- Terminal app owns an interactive session.
- Pipes connect app output to another process or terminal buffer.

**Acceptance:**

- A CLI smoke app writes stdout and the terminal displays it.

## FR-SOS-016: Permissions or Capabilities

**Goal:** Prevent apps from accessing all OS resources by default.

**Requirements:**

- Manifests declare required file, IPC, device, and network capabilities.
- Kernel checks capabilities at syscall dispatch.
- Denials return consistent permission errors.

**Acceptance:**

- An app without file-write capability cannot write `/etc` or `/sys/apps`.

## FR-SOS-017: Networking API

**Goal:** Expose networking to apps through OS services.

**Requirements:**

- Define socket or network-service APIs.
- Keep NIC drivers below the app boundary.
- Support nonblocking or timeout-capable operations.

**Acceptance:**

- A network smoke app can open a connection or issue a local network-service
  request without direct driver access.

## FR-SOS-018: App Manifest and Package System

**Goal:** Make app identity and launch metadata explicit.

**Requirements:**

- Manifests define app id, executable path, icon, permissions, args,
  dependencies, and GUI/CLI/service mode.
- Launcher reads manifests from filesystem, not hardcoded resident tables.
- Missing or invalid manifests produce visible launch errors.

**Acceptance:**

- Adding a manifest and executable to the disk image makes a new app visible to
  the launcher without code changes.

## FR-SOS-019: Debuggability

**Goal:** Make process-backed app failures diagnosable.

**Requirements:**

- Provide process list, syscall trace, kernel log, crash dump, and fault decode.
- Include app id, PID, path, trap number, fault address, and exit code.
- Keep diagnostics available in serial/QEMU tests.

**Acceptance:**

- A forced app fault produces a readable process crash report and does not hide
  the failing PID.

## FR-SOS-020: Whole-File Multi-Cluster Exec Read Into a Dedicated Identity-Mapped DMA Buffer

**Goal:** Read the ENTIRE executable (every cluster, following the FAT32
next-cluster chain) into one dedicated, identity-mapped, byte-contiguous DMA
buffer so any real program (>4096B) loads without truncation and stays
mmio-parseable by the ring-3 handoff. Tightens FR-SOS-001, which today reads
only the first cluster.

**Requirements:**

- Port the FAT-chain loop of the boxed-`[u8]` `_vfs_boot_read_file_chain` into
  the coherent raw path: walk clusters via `_vfs_boot_fat32_next_cluster`, DMA
  each cluster from `_vfs_boot_fat32_cluster_lba` via
  `read_shared_dma_in_namespace_on_queue` into destination offset
  `i*cluster_bytes` of a single buffer.
- Contiguity is of the DESTINATION buffer, not the disk: on-disk clusters may be
  fragmented; the assembled buffer must be byte-contiguous over `[0..file_size)`.
- The exec buffer MUST be a dedicated allocation distinct from the reused
  4096-byte dirent scratch (`g_boot_fat32_scratch`), which stays only for
  directory-sector reads; reusing it re-truncates and clobbers before handoff.
- The buffer MUST be identity-mapped (cpu_virt == host_phys) so
  `x86_64_fs_exec_enter_image_ring3` can mmio-parse PT_LOADs off it, and MUST
  survive pmm/vmm/user-AS churn until the iretq (single owner, freed only after
  exec completes or fails).
- Replace the single-cluster `_vfs_boot_read_file_chain_raw` for the exec read
  path.

**Acceptance:**

- The proven 2-cluster FSEXEC.ELF (4728B) driven through the SHELL exec path
  reaches its `rc=42` exit marker over serial.
- Serial shows assembled length equal to the dirent-declared size for a >4096B
  ELF (`len=4728`, not 4096).
- Ring-3 parse markers `[spawn] phoff=... phentsize=... phnum=...` decode to sane
  values (bytes past offset 4096 present and correct).
- A byte sampled at buffer offset 4096 equals the on-disk second-cluster first
  byte.

**Milestone:** M1

**Depends:** none

**Anchors:** src/os/services/vfs/vfs_boot_init.spl:625, :552, :490, :487, :440, :620

## FR-SOS-021: Registry-Free Arbitrary-Path 8.3 Resolution + Nested Directory Traversal

**Goal:** Resolve ANY filesystem path to its bytes by mangling each path
component to canonical FAT 8.3 and walking directories generically on the
coherent raw channel, so unregistered arbitrary paths run — not only
hardcoded/app-registry names. Tightens FR-SOS-013, which today exposes only
registered `/bin` and `/sys/apps` names via a hardcoded ladder.

**Requirements:**

- Add a generic raw/mmio 8.3 comparator: generalize
  `_vfs_boot_dirent_matches_short_name_raw` / `_vfs_boot_dirent_name11_raw` to
  compare the 11 mmio dirent bytes against the EXISTING generic mangler
  `_vfs_boot_fat83_short_name_key(leaf)` instead of the fixed literal ladder.
- Do NOT route through the boxed-`[u8]` comparator
  `_vfs_boot_dirent_matches_short_name`: the coherent handoff requires the
  scratch/mmio channel; only the mangler is reusable across channels.
- Replace the hardcoded registry map `_vfs_boot_short_name_for_path` and the
  per-path special-case ladder in `vfs_boot_read_pure_nvme_fat32_path_bytes` with
  a recursive component walk: split on `/`, call `_vfs_boot_find_dirent_cluster_raw`
  with `want_dir=true` per interior component, then read the leaf (want_dir=false)
  via the whole-file reader.
- Resolution MUST NOT consult `app_registry_*`; an unregistered leaf and
  unregistered intermediate directories resolve purely from on-disk 8.3 dirents.

**Acceptance:**

- An unregistered nested non-/sys/apps path (e.g. `/A/B/HI.ELF`) with no
  app_registry entry resolves and reads `len>0`; serial shows the computed 8.3
  leaf and per-component directory-cluster hits.
- The same binary at an arbitrary path runs to its exit marker via the shell with
  no registry/manifest edit.
- A missing intermediate directory or missing leaf yields empty bytes (len 0) and
  a negative-errno exec result, never a wrong-file match.

**Milestone:** M1

**Depends:** none

**Anchors:** src/os/services/vfs/vfs_boot_init.spl:696, :647, :634, :499, :569

## FR-SOS-022: Single-Source Coherent (bytes, blob) Exec Read Seam

**Goal:** Make the `[u8]` bytes handed to the loader and the raw blob address the
ring-3 handoff mmio-parses come from ONE identity-mapped buffer, eliminating the
rc=-5 blob-zero failure caused by the unbacked `simpleos_fat32_*` seam.

**Requirements:**

- Rewrite `_x86_64_read_spawn_bytes_and_blob` to call the pure-Simple whole-file
  reader (FR-SOS-020's dedicated-buffer reader, exposed like
  `vfs_boot_read_pure_nvme_fat32_path_bytes`) and return
  `(rt_bytes_from_raw(buf,len), buf)` where `buf` is that buffer's
  identity-mapped address.
- Remove reliance on the phantom externs `simpleos_fat32_stream_open` /
  `simpleos_fat32_stream_read_at` / `simpleos_fat32_path_read_buffer_addr` —
  unbacked and DCE-stubbed on every target; today the buffer-addr extern returns
  a nonzero-but-unpopulated .bss static that passes the nonzero gate yet fails
  the ELF magic check.
- Read-time validation is minimal: mmio ELF magic (0x464C457F) at blob offset 0
  and `bytes.len()==file_len` coherence, before
  `x86_64_fs_exec_handoff_blob_ready`. Do NOT duplicate phdr/segment bounds
  (those live in the ring-3 handoff and FR-SOS-005/026).
- The returned blob physically backs the returned bytes (one source of truth), so
  a coherent read can never present ELF-magic bytes while the blob channel is
  zero.

**Acceptance:**

- For a valid FS ELF, `[spawn] FAIL raw blob address is 0` and
  `[spawn] FAIL blob not ELF ...` NEVER appear; handoff proceeds to
  `[spawn] PT_LOAD segments mapped` then `[spawn] entering user cs=0x2b`.
- `[fs-exec] x86_64:handoff-return path=... rc=...` no longer reports rc=-5 for an
  on-disk ELF the pure-Simple reader can read.
- Serial confirms `bytes.len()` equals the blob-derived file length at the seam.

**Milestone:** M1

**Depends:** FR-SOS-020, FR-SOS-021

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_spawn.spl:16, :30, src/os/services/vfs/c_nvme_block_adapter.spl:25, src/os/kernel/loader/x86_64_fs_exec_ring3.spl:291, src/os/services/vfs/vfs_boot_init.spl:738

## FR-SOS-023: Exec-Read Size Ceiling and Fail-Closed Integrity Handling

**Goal:** Bound the exec read at a configured maximum and fail closed on any
read-integrity fault (oversize, short read, missing, non-ELF), freeing the
dedicated buffer so repeated failed shell commands never fault, leak, or
partially load. Tightens FR-SOS-001 with read-TIME bounds distinct from the
whole-file assembly of FR-SOS-020.

**Requirements:**

- Enforce a hard exec-image ceiling using the existing
  `FAT32_PATH_READ_BUFFER_MAX` (4194304): a file whose dirent-declared size
  exceeds the ceiling is rejected before allocation/DMA with a negative errno and
  a bounded serial marker — no partial read, no OOM, no fault.
- Verify integrity after assembly: total bytes DMA'd must equal the
  dirent-declared size (no short read from a truncated/early-end chain); mismatch
  fails closed with a distinct marker.
- Extend the existing missing-file / non-ELF negative surfaces to the new reader
  so truncation is a failure, not the current silent `min(size,4096)` copy.
- Free/return the dedicated exec DMA buffer on ANY failed exec so N consecutive
  failing shell commands do not exhaust DMA memory (single-owner per attempt).

**Acceptance:**

- A file larger than 4 MiB (the clang binary, ~119 MB) is rejected with a bounded
  `oversize`/ceiling marker and a negative rc, with no 119 MB allocation and no
  fault (this is the M3 clang unblock even though the guard lands at M1).
- A deliberately truncated on-disk chain (declared size > readable clusters)
  yields a negative rc and a short-read marker, not a partially mapped image.
- A missing arbitrary path yields rc=-2 (`[fs-exec] spawn:resolve-fail`); 100
  consecutive missing/oversize exec attempts complete with stable DMA free-memory
  (no monotonic leak) and no triple-fault.

**Milestone:** M1

**Depends:** FR-SOS-020

**Anchors:** src/os/services/vfs/c_nvme_block_adapter.spl:30, src/os/kernel/loader/x86_64_fs_exec_spawn.spl:18, src/os/services/vfs/vfs_boot_init.spl:631, src/os/kernel/loader/x86_64_fs_exec_ring3.spl:188

## FR-SOS-024: Production-Boot Ring-3 Privilege Wiring (TSS.rsp0/LTR + DPL3 User GDT + SYSCALL MSRs)

**Goal:** Install and verifiably reach every ring-3 privilege prerequisite —
TSS.rsp0 via `ltr`, DPL3 user GDT selectors matching the handoff's cs=0x2b/ss=0x23,
and SYSCALL LSTAR/STAR/SFMASK + EFER.SCE + a kernel syscall stack — on the
PRODUCTION boot sequence that hosts the shell/SSHd, before the first ring-3
handoff, so the iretq to CPL3 and the first ring-0 trap taken from CPL3 do not
#GP or triple-fault. Tightens FR-SOS-008. Merges the previously separate
ring3/proc-life/shell-ssh privilege-init requests into one wiring item.

**Requirements:**

- Call `rt_x86_tss_init()` exactly once on the boot CPU during the production
  boot_fs / arch_init / limine service-init sequence (fills the crt0.s
  gdt64_tss_desc slot 0x30, executes `ltr $0x30`, installs an rsp0 kernel stack);
  guard idempotently. Today `rt_x86_tss_init`, `gdt_init`, and
  `gdt_set_kernel_stack` have ZERO src/os callers (only harness entries).
- Guarantee `install_syscall_entry()` (EFER.SCE, STAR, LSTAR, SFMASK) runs on the
  boot path before any ring-3 exec; today its only caller
  `arch_x86_64_early_init` is itself invoked only by example entries, so on the
  production shell boot LSTAR/STAR/SFMASK are never programmed.
- Ensure `_kernel_syscall_stack_top` points at a valid mapped kernel stack before
  the first ring-3 `syscall` (the trampoline switches to it, independent of
  TSS.rsp0). TSS.rsp0 MUST point at a valid mapped kernel stack distinct from the
  interrupted CPL3 user stack; a single shared rsp0 stack is acceptable at M1
  (single-depth synchronous exec) — per-task kernel stacks are deferred.
- Confirm the active DPL3 selectors (cs=0x2b -> user CS64 0x28|3, ss=0x23 ->
  user DS 0x20|3) match the handoff frame and the GDTR limit spans the 16-byte
  TSS descriptor at 0x30. Eliminate the dead/parallel unreferenced `gdt_init`
  path (wire it or remove it).
- Fail-closed: if LTR, the TSS descriptor patch, or the MSR install cannot
  complete, log a decoded reason and refuse ring-3 exec rather than proceeding
  into a triple-fault. This item UNBLOCKS FR-SOS-014 (preemption needs a ring-0
  stack) and FR-SOS-019 (fault frame needs the trap not to triple-fault).

**Acceptance:**

- Production boot serial prints `[tss] rsp0 installed sel=0x30` and
  `[syscall] MSRs programmed: LSTAR STAR SFMASK=0x200` (and a
  `[gdt] user cs=0x2b ss=0x23 ... ltr ok` marker) BEFORE the first
  `[shell-exec] exec:` line; `ltr $0x30` executes without #GP.
- A shell `exec /FSEXEC.ELF` reaches `[spawn] entering user cs=0x2b` and the
  payload prints `FSEXEC_OK rc=42` — ring 3 reached from the SHELL, not the
  harness.
- A ring-3 payload that loops past one timer tick does not reset QEMU (no
  triple-fault); a deliberate ring-3 fault is caught on rsp0 and decoded, not a
  triple-fault reboot.

**Milestone:** M1

**Depends:** FR-SOS-008 (tightens)

**Anchors:** src/os/kernel/boot/boot_fs.spl:84, src/os/kernel/arch/x86_64/arch_init.spl:69, src/os/kernel/arch/x86_64/cpu.spl:185, src/os/kernel/interrupts/gdt.spl:152, :205, src/os/kernel/boot/limine_boot.spl:406, examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:15489, crt0.s:643

## FR-SOS-025: Fail-Closed Spawn — Route Generic Exec Through the Arch Ring-3 Handoff, No Phantom Pid

**Goal:** Wire the generic shell spawn path through the arch ring-3 handoff and
make every spawn entry point fail closed: no API returns a positive pid unless a
user address space was actually built and control transferred to (or scheduled
for) ring 3. Tightens FR-SOS-005. This FR breaks the circular-import block that
today leaves `shell_exec` on the phantom generic path.

**Requirements:**

- PRIMARY: route the generic `fs_exec_spawn` / `fs_exec_spawn_as` /
  `fs_exec_prepare_spawn` path through the arch ring-3 handoff
  (`fs_exec_spawn_ring3` -> `x86_64_fs_exec_spawn`), resolving the circular
  import so `shell_exec` reaches `x86_64_fs_exec_enter_image_ring3`. Today the
  generic path registers a bootstrap TCB and returns a phantom pid, never maps
  PT_LOADs, and never enters ring 3.
- On any non-handoff arch or unbuilt image, return a negative "not-executed"
  errno, mirroring `if handoff_rc < 0: return handoff_rc`; never surface a
  cosmetic pid as success.
- The bootstrap pid from `fs_exec_prepare_spawn_from_bytes` MUST be flagged
  non-runnable/cosmetic and never reported to the shell as success until a real
  handoff or scheduler-run exists.
- Emit `[fs-exec] spawn:fail ... rc=<neg>` on every failure path; a success
  marker is emitted ONLY after ring-3 entry. Keep the repo free of any phantom
  placeholder symbol (e.g. `*spawn_static_seeded*`).

**Acceptance:**

- Calling generic `fs_exec_spawn(path,...)` on a non-x86_64-handoff arch returns
  rc<0 (never a positive pid).
- Shell `exec` of a bad/missing/oversized file prints a negative rc and returns
  to the prompt; no cosmetic pid is printed as success.
- A repo test fails the build if any `*spawn_static_seeded*`-style phantom
  placeholder is reintroduced into src/os.

**Milestone:** M1

**Depends:** FR-SOS-005 (tightens), FR-SOS-002

**Anchors:** src/os/kernel/loader/fs_exec_spawn.spl:276, :286, :247, src/os/kernel/loader/x86_64_fs_exec_spawn.spl:90, src/os/apps/shell/exec.spl:40

## FR-SOS-026: Full ELF64 Header + Entry-Point Bounds Validation Before Mapping

**Goal:** Map only well-formed ELF64 x86-64 executables: validate every
structural header/segment field against the known file length and the mapped
ranges before any address space is built, each rejection returning a unique
fail-closed rc. Tightens FR-SOS-005, which trusts these fields on the raw-blob
parse path (today only e_ident magic and EI_CLASS are checked).

**Requirements:**

- Validate the full ELF header: EI_DATA little-endian, e_type in {ET_EXEC,
  ET_DYN}, e_machine==EM_X86_64 (62), e_version==1, e_ehsize>=64,
  e_phentsize==56, e_phnum within a sane cap (<=64).
- Validate the parsed e_entry falls inside a mapped, executable (user_rx)
  PT_LOAD range; reject otherwise.
- Per segment: require p_memsz>=p_filesz, p_align a power of two, guard
  p_offset+p_filesz against u64 wrap; extend the existing file-range bound to the
  phdr entry read offsets.
- Each rejection returns a UNIQUE negative rc plus `[spawn] FAIL <reason>` and
  leaves NO partially-mapped address space (reject/tear down before mapping).

**Acceptance:**

- A truncated/garbage ELF, an ELFCLASS32 file, an e_machine!=x86-64 file, and an
  entry-out-of-range file each emit a DISTINCT `[spawn] FAIL ...` with rc<0 and no
  `[spawn] entering user`.
- The proven FSEXEC.ELF passes all checks and enters ring 3.
- No address-space frames remain mapped after a rejected ELF (verified via the
  user-AS-teardown free-page marker).

**Milestone:** M1

**Depends:** FR-SOS-005 (tightens)

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_ring3.spl:294, :187, :200, :302

## FR-SOS-027: PT_LOAD User-Range + W^X Permission Enforcement in the FS-Exec Mapper

**Goal:** Fail closed on any PT_LOAD that would place user-accessible (especially
user-writable) mappings outside the user canonical range, over
kernel/identity/MMIO memory, or as a write+execute page, so a corrupt or hostile
ELF cannot obtain a user_rw mapping over kernel memory. Tightens FR-SOS-003,
which maps at raw p_vaddr with no range guard.

**Requirements:**

- In `_map_pt_loads`, validate each PT_LOAD `[p_vaddr, p_vaddr+p_memsz)` lies
  fully inside the loader's user-program window and does NOT overlap the
  `vmm_clone_kernel_low_identity` range, MMIO windows, or the reserved user-stack
  region; reject with a distinct marker otherwise.
- Reject (return 0) any PT_LOAD whose p_flags contain BOTH PF_W and PF_X; the
  current per-page union silently maps such a segment user_rw and drops X without
  flagging the W^X violation.
- Assert emitted PTEs realize W^X: writable pages carry NX (VmFlags.user_rw sets
  VM_NO_EXECUTE) and executable pages are read-only (user_rx); add a per-page
  audit marker proving 0 pages are simultaneously WRITABLE and !NX.
- Cap the total mapped-image span / page count (from lo_page/hi_page) so an
  oversized span cannot exhaust the PMM.

**Acceptance:**

- A crafted ELF whose PT_LOAD p_vaddr targets a kernel/identity/MMIO address
  emits `[spawn] FAIL segment vaddr out of user range` and rc<0 with NO
  `[spawn] entering user`.
- An ELF with a PF_W|PF_X PT_LOAD emits `[spawn] FAIL W^X violation` and rc<0.
- The proven FSEXEC.ELF still emits `[spawn] PT_LOAD segments mapped` and reaches
  ring 3; the per-page audit reports 0 writable&&executable pages.

**Milestone:** M1

**Depends:** FR-SOS-003 (tightens)

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_ring3.spl:172, :238, :214, src/os/kernel/types/memory_types.spl:74

## FR-SOS-028: FS-Exec Fault Decode (Error-Code, Pid, Region) — Diagnose, Never Silently Triple-Fault

**Goal:** When an FS-exec ring-3 process faults, decode and log the full fault
context (pid, faulting address, x86 error-code bits, RIP, region) so FS-exec
faults are diagnosable instead of resetting the VM with no output. Tightens
FR-SOS-019, which prints only CR2/RIP/RSP and halts. (Actual task-scoped
termination is FR-SOS-038, gated on return-to-caller.)

**Requirements:**

- `_isr_page_fault` MUST receive and decode the CPU-pushed #PF error code
  (present/write/user/reserved/instruction-fetch bits); today the handler
  signature and `idt_set_handler(VEC_PAGE_FAULT,...,0)` drop the error code.
- Emit one structured marker
  `[fault] pid=<pid> cr2=0x<addr> err=<decoded P|W|U|I|R> rip=0x<rip> rsp=0x<rsp> region=<image|stack|heap|unmapped>`,
  resolving pid from the current user task and region from the faulting AS's
  mappings (not the stale global vmspace).
- On a user-mode (err.U=1) unhandled fault, do NOT `_halt()` the kernel: mark the
  process faulted and, pre-scheduler, at minimum print the full decode before
  halting; once scheduler-resume exists (FR-SOS-038) return control to the shell.
- Extend the same decode to the other CPL3-reachable vectors (#GP, #SS, #NP) so a
  missing-TSS / bad-selector iretq surfaces a marker instead of a silent
  triple-fault.

**Acceptance:**

- A user program dereferencing an unmapped user address prints exactly one
  `[fault] pid=.. cr2=.. err=...U... rip=.. region=unmapped` line; the kernel
  continues, or pre-scheduler halts only AFTER printing the full decode.
- A #GP from a bad ring-3 transition prints `[fault] #GP ...` rather than
  resetting the VM with no output.
- The decoded write/user/instruction-fetch bits match the injected fault type.

**Milestone:** M1

**Depends:** FR-SOS-002, FR-SOS-019 (tightens)

**Anchors:** src/os/kernel/interrupts/idt.spl:374, :132, :385, src/os/kernel/arch/x86_64/cpu.spl:73

## FR-SOS-029: Pure-Simple FAT32 Bake Produces Guest-Mountable Images

**Goal:** Make `src/os/port/disk_image.build` emit FAT32 images the guest reader
mounts and reads on its own, removing the correctness dependency on the opt-in
host mkfs.fat+mcopy fast-path that only exists because the interpreter builder was
non-conformant (BUG-FAT32-BAKE-FATSIZE-TOO-SMALL).

**Requirements:**

- The pure-Simple builder (`_build_bpb` / `_build_fat`) MUST compute a fat_size
  large enough for the actual cluster count so the image passes fsck.fat and
  mounts under the guest VFS boot probe — no reliance on
  `build/os/.bake_use_mkfs_fat` for a correct image.
- Flat-root and nested (guest_path) payloads MUST both lay out contiguously from
  cluster 3 with correct FAT chains for multi-cluster files.
- The bake harness MUST NOT silently fall back to a non-conformant image: if the
  pure-Simple builder cannot produce a conformant image it fails closed with a
  diagnostic.
- Emitted BPB geometry (bytes_per_sector, sectors_per_cluster) MUST be parseable
  by the guest FAT32 boot reader (BPB-driven), verified by an actual guest mount.

**Acceptance:**

- Host: `bin/simple run src/os/port/disk_image_bake.spl` with NO
  `build/os/.bake_use_mkfs_fat` marker produces an image that `fsck.fat -n`
  reports clean and `mdir` lists all expected payloads at their guest paths.
- QEMU: booting the pure-Simple-built image reaches the VFS mount-success marker
  without the host mkfs fast-path having run.
- Regression: byte-identical flat-root layout is preserved when nested_payloads
  is empty (hash compare against the prior conformant image).

**Milestone:** M1

**Depends:** none

**Anchors:** src/os/port/disk_image_bake.spl:17, :285, src/os/port/disk_image.spl:124, :196, :210

## FR-SOS-030: Post-Bake Host Validation Harness for the FAT32 Disk Image

**Goal:** Add a host-side step that verifies the baked FAT32 image actually
contains each expected artifact at its guest path with coherent, complete bytes
and correct ELF format BEFORE QEMU boots, catching the zero-blob and
single-cluster-truncation failure classes at bake time instead of as an in-guest
rc=-5. Tightens FR-SOS-019 (whose diagnostics today only cover the initramfs, not
the FAT32 disk).

**Requirements:**

- After `build()`, walk the FAT32 image on the host and assert every expected
  payload (e.g. `/FSEXEC.ELF`, `/usr/bin/hello`, `/usr/bin/clang`) resolves at its
  declared guest_path.
- For each resolved payload, read the WHOLE file back and byte-compare against the
  source bytes (multi-cluster coherence), failing if any cluster is zero-filled or
  truncated.
- For ELF payloads, assert ELF magic, ELFCLASS64, and absence of PT_INTERP;
  report file_size vs FAT directory-entry size mismatch.
- Emit a machine-checkable PASS/FAIL summary and exit nonzero on any failure so
  CI and the bake pipeline gate on it (mirror initramfs validate_image).

**Acceptance:**

- Injecting a deliberately zeroed payload region makes the validator exit nonzero
  with `bytes mismatch at cluster N`; a coherent image exits 0.
- Validator output lists each expected guest path with resolved=yes, size=match,
  elf=ok/no-interp.
- A multi-cluster payload (>4096B) reads back byte-identical; a truncated image is
  rejected; the bake `main()` aborts (no `bake done`) when validation fails.

**Milestone:** M1

**Depends:** FR-SOS-019 (tightens)

**Anchors:** src/os/port/disk_image_bake.spl:79, :306, :182, src/os/port/disk_image.spl:258

## FR-SOS-031: Bake a Real Simple-Compiled Freestanding ELF as the FS-Exec Proof Artifact

**Goal:** Replace the hand-written assembly FSEXEC payload with a genuine
Simple-source-compiled, freestanding x86_64-unknown-simpleos static ELF, baked at
`/FSEXEC.ELF` and at a shell-resolvable path (`/usr/bin/hello`), so the FS-exec
proof runs a Simple-origin program.

**Requirements:**

- Compile a minimal Simple program to a static x86_64-unknown-simpleos ELF via
  the seed native-build path, syscall-only (write(1,...) then exit(0)) — NO libc,
  NO PT_INTERP (the argv/auxv + libc _start frame is out of scope here; see
  FR-SOS-041/046).
- Emit the ELF as a committed build recipe producing `build/os/<name>/hello.elf`
  and asserting ELFCLASS64, entry at the linker base, and absence of PT_INTERP.
- Bake it at `/FSEXEC.ELF` (replacing the asm fsexec_hello.elf) AND at
  `/usr/bin/hello` via the pure-Simple nested-payload path so it resolves through
  `shell_path_search`.
- The artifact MUST exercise the multi-cluster case if >4096B so the proof covers
  real programs.

**Acceptance:**

- Host: `readelf -h` shows Class=ELF64, no PT_INTERP, and Simple-toolchain
  provenance (not the fsexec_hello.S asm).
- QEMU: the image containing the Simple-origin `/FSEXEC.ELF` prints ring-3 proof
  and `FSEXEC_OK rc=42` (syscall 60) in the serial log.
- Host: an image-content walk shows the same ELF bytes at both `/FSEXEC.ELF` and
  `/usr/bin/hello`.
- Shell-dispatch: once generic spawn reaches the arch handoff (FR-SOS-025),
  typing `hello` at the guest shell prints the program output.

**Milestone:** M1

**Depends:** FR-SOS-020, FR-SOS-025

**Anchors:** build/os/elfexec/build-fsexec-img.spl:6, examples/09_embedded/simple_os/arch/x86_64/fs_elf_exec_smoke_entry.spl:11, examples/01_getting_started/hello_native.spl, scripts/os/simpleos-native-build.shs:1, src/os/apps/shell/path_search.spl:14, src/os/port/disk_image_bake.spl:182

## FR-SOS-032: Canonical Positive Serial-Marker Contract for Real-Process Launch + Exit Code

**Goal:** Define a single source of truth for greppable markers that POSITIVELY
prove a real user-mode (CPL3) process launch and a process exit with code, and
make `classify_serial` REQUIRE them for fs-exec lanes. Today
`fs_exec_fallback_contract` only NEGATIVELY rejects two fallback strings, and
`classify_serial` passes on SMF markers with no launch/exit proof.

**Requirements:**

- Add a positive-contract module (peer of `fs_exec_fallback_contract`) defining
  canonical markers: a RING3_ENTER proof written from user mode and a
  `PROC_EXIT pid=<n> code=<n>` marker with a parseable code.
- `classify_serial()` for fs-exec lanes returns pass only when the CPL3-entry
  marker AND a PROC_EXIT marker (with expected code) are both present, in addition
  to the existing fallback rejection.
- Expose a helper that extracts the exit code from serial so specs can assert
  exact codes.
- Wire the new required markers into `qemu_scenario_serial_acceptance_reason` so
  name-based lanes inherit the positive contract.

**Acceptance:**

- Unit spec on synthetic serial: pass only when both CPL3-entry and PROC_EXIT(code)
  present; missing either returns a specific `boot-fail:<marker>`.
- The exit-code extractor returns 42 from `PROC_EXIT pid=1 code=42` and errors on
  an absent marker.
- Serial with `standard_smf_markers()` but no PROC_EXIT is classified boot-fail,
  not pass.

**Milestone:** M1

**Depends:** none

**Anchors:** src/os/fs_exec_fallback_contract.spl:14, src/os/qemu_systest_contract.spl:37, src/os/_QemuRunner/scenario_exec.spl:722, src/os/kernel/loader/x86_64_fs_exec_ring3.spl:366

## FR-SOS-033: Production-Shell Real Ring-3 FS-Exec Acceptance Lane From an Arbitrary Path

**Goal:** Add a self-terminating QEMU systest lane that boots the production
kernel, has the SHELL (`shell_exec` dispatch, not a test entry) execute a Simple
ELF placed at an ARBITRARY filesystem path (e.g. `/bin/hello`, NOT a registered
`/sys/apps/<name>`), and passes only when serial proves a genuine CPL3 run plus a
process exit code.

**Requirements:**

- Create a bootable kernel build target whose init path drives `shell_exec` on a
  NON-registered arbitrary path (leaf mangled to 8.3 via dir-walk), not an
  app_registry entry.
- Package a small Simple hello ELF into the FAT32 image at an arbitrary path that
  emits a CPL3-only proof token from user mode then exits via syscall 60.
- Register the lane in `qemu_systest_contract` with a NEW required-marker set
  distinct from `standard_smf_markers()`; SMF/resident-manifest markers MUST NOT
  satisfy this lane.
- QEMU self-terminates via isa-debug-exit on the process-exit marker; timeout,
  #GP, or triple-fault classifies RED (never pass-on-timeout, never `skip()`).
  Missing kernel/image is a diagnosed RED.

**Acceptance:**

- Serial contains, in order: `[spawn] entering user cs=0x2b`, a CPL3-only proof
  token from user mode, then a process-exit marker with the expected code.
- `run_qemu_systest` classification == pass ONLY when all three appear; serial
  with just `standard_smf_markers()` returns boot-fail; a hang yields RED.
- The path used is not present in app_registry (registration-free exec).

**Milestone:** M1

**Depends:** FR-SOS-032

**Anchors:** test/03_system/os/qemu/sys_qemu_x86_64_fs_exec_spec.spl:39, src/os/qemu_systest_contract.spl:247, :69, examples/09_embedded/simple_os/arch/x86_64/fs_exec_general_ring3_entry.spl:78, src/os/apps/shell/exec.spl:40

## FR-SOS-034: Phantom-Pid Regression Guard — A Registered Pid Is Never Evidence Without a Real Ring-3 Run

**Goal:** Guarantee the harness FAILS if a positive pid can be produced without a
genuine ring-3 entry, and that the shell structurally cannot route to the phantom
generic path. Tightens FR-SOS-002. Replaces the current source-grep string checks
with a behavioral + structural guard.

**Requirements:**

- Acceptance rule: a serial showing `[fs-exec] spawn:pid=N`/`spawn:prepared`
  WITHOUT the CPL3 entry marker and PROC_EXIT is classified FAIL, not pass.
- Runtime invariant spec: in a real lane run, pid>0 implies the CPL3 proof marker
  appears in the same serial (phantom pid without user-mode entry = RED).
- Structural guard spec: `shell_exec` MUST dispatch through `fs_exec_spawn_ring3`
  (the handoff path) and NEVER call the generic `fs_exec_spawn` /
  `fs_exec_spawn_as` bootstrap-TCB path — the guard goes RED if `exec.spl` reverts.
- Replace the source-grep `x86_64_fs_exec_spawn_spec` string checks with the above
  behavioral guard so the invariant is proven by a run.

**Acceptance:**

- Injecting a phantom-only serial (spawn:pid present, no CPL3/PROC_EXIT) into the
  classifier returns fail.
- The dispatch-guard spec goes RED if `exec.spl` routes to `fs_exec_spawn` instead
  of `fs_exec_spawn_ring3`.
- A real lane run reports pid>0 AND the CPL3 entry marker together, or the lane
  fails.

**Milestone:** M1

**Depends:** FR-SOS-032, FR-SOS-002 (tightens)

**Anchors:** src/os/kernel/loader/fs_exec_spawn.spl:268, :248, :288, src/os/apps/shell/exec.spl:40, test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl:11

## FR-SOS-035: Real-Run Negative Fail-Closed Acceptance Suite (Truncated / Missing / Unregistered / Zero-Blob)

**Goal:** Replace the inline SIMULATION (`exec_from_fs_spec` `simulate_fs_exec_spawn`
returning fake pid=42) with real-dispatch negative fixtures. Each malformed case
yields a documented negative rc and a specific FAIL diagnostic on serial, and the
lane classifies each as a controlled failure with NO ring-3 entry marker. Tightens
FR-SOS-005.

**Requirements:**

- Provide FAT32 fixtures for: truncated ELF (<64B and 1-byte), missing file, a
  valid-but-unregistered nonexistent path, and a nonzero-but-zero-content blob (the
  magic-check case).
- Assert `shell_exec` returns the contract codes (-1 not-found, -2 resolve, -5
  bad/zero blob, -8 image-build) and serial shows the matching
  `[fs-exec] spawn:*` / `[spawn] FAIL *` diagnostic.
- For every negative case assert the CPL3 proof marker and `[spawn] entering user`
  are ABSENT (fail closed, no partial ring-3 transfer).
- Retire or clearly demote `exec_from_fs_spec`'s `simulate_fs_exec_spawn` so a fake
  pipeline can no longer stand in for acceptance evidence.

**Acceptance:**

- Each negative fixture: serial contains its specific FAIL diagnostic AND lacks any
  CPL3 entry marker; classification is a controlled boot-fail, not pass.
- Returned rc equals the documented code per case.
- The zero-content-blob fixture reproduces the rc=-5 magic-check path and fails
  closed.

**Milestone:** M1

**Depends:** FR-SOS-032, FR-SOS-005 (tightens)

**Anchors:** test/01_unit/os/kernel/loader/exec_from_fs_spec.spl:93, src/os/kernel/loader/fs_exec_spawn.spl:235, src/os/kernel/loader/x86_64_fs_exec_ring3.spl:291, :189, src/os/apps/shell/exec.spl:20

## FR-SOS-036: Process Exit Returns to the In-Kernel Exec Caller via Scheduler Resume (Retire out 0xf4)

**Goal:** Make a ring-3 fs-exec process that calls exit hand control back to the
in-kernel exec caller (the shell or SSHd) via scheduler resume, record the exit
status, and drop IOPL=3 — instead of terminating the guest via `out 0xf4`
isa-debug-exit — so a command over the shell or SSH prints its output and returns
a prompt, and multiple sequential commands run on one boot. Tightens FR-SOS-009.
Merges the previously separate ring3 / proc-life / ssh "return-to-shell" requests.

**Requirements:**

- Capture a kernel resume context (kernel rsp/rbp/return address + callee-saved
  regs) immediately before `arch_x86_64_enter_user_task` / `rt_x86_enter_user_first`
  (today "does not return"); make the enter a BLOCKING primitive, implemented on the
  reserved-but-unimplemented case 14 `spl_handle_enter_user_blocking` (currently an
  ENOSYS weak stub), not a parallel path.
- The exit syscall MUST restore that context and return the exit code up through
  `x86_64_fs_exec_enter_image_ring3` -> `x86_64_fs_exec_spawn` -> `fs_exec_spawn_ring3`
  to the caller, overriding the weak `spl_handle_exit` (whose body is
  `outb(0xF4,(status<<1)|1); cli; hlt`).
- Pin the exit ABI: the crt `_exit` emits BOTH Linux exit(60) and SimpleOS exit(0)
  while the dispatcher maps case 0->exit and case 60->debug_write; exactly one
  number is terminate-and-return-to-caller and the debug_write(60) path must not
  corrupt/double-report the status byte.
- Fix the single-scheduler defect: the spawned ring-3 task MUST register in the SAME
  scheduler the exit/wait path uses (`g_shim_scheduler`), not the throwaway
  `_fs_exec_new_bootstrap_scheduler`, or exit can never reach the shell's context.
- Set user rflags to IF-only (0x202) instead of 0x3002, removing IOPL=3 so ring-3
  code cannot execute port I/O — achievable only once exit no longer needs user
  `out 0xf4`. After regaining control, the caller (local shell OR SSHd session)
  re-issues its prompt and accepts the next command on the same session; QEMU
  terminates only on client disconnect, not on child exit.

**Acceptance:**

- Shell `exec /FSEXEC.ELF` returns to a live prompt after the program exits; serial
  shows `[exit] pid=N code=K return-to-caller` and the shell accepting a NEXT
  command (no `out 0xf4` on clean exit).
- Over SSH, two sequential commands (`/sys/apps/hello` then `whoami`) each produce
  output + exit-status, the prompt returns between them, and the session stays open.
- A second consecutive exec in one session proves control genuinely returned (not a
  fresh boot); the bootstrap pid is observably waited on, not discarded.

**Milestone:** M2

**Depends:** FR-SOS-024, FR-SOS-002, FR-SOS-012, FR-SOS-009 (tightens)

**Anchors:** examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:15642, :15747, src/os/kernel/arch/x86_64/context.spl:39, src/os/kernel/loader/x86_64_fs_exec_ring3.spl:361, :367, src/os/kernel/loader/fs_exec_spawn.spl:247, src/os/libc/simpleos_cxxabi.c:282, src/os/apps/shell/exec.spl:40

## FR-SOS-037: Propagate Real Child Exit Status to the Spawn Caller and wait/reap

**Goal:** Thread the ring-3 child's actual exit status back through the spawn call
and the wait/reap path so the shell can report `$?` and a parent can reap an exited
child, replacing the cosmetic phantom pid. Tightens FR-SOS-009 / FR-SOS-002.

**Requirements:**

- `fs_exec_spawn_ring3` and `x86_64_fs_exec_spawn` MUST return the child's real exit
  code (0..255) on clean exit; today they return the cosmetic pid on success.
- The captured exit status MUST be recorded in a reap slot keyed by pid so a
  subsequent wait (syscall 3) or waitpid (syscall 61) returns exited(code); the slot
  distinguishes "still running" from "exited(code)".
- The shell MUST surface the reaped status as `$?`.
- Reaping an exited child MUST release its scheduler/zombie slot so repeated exec
  does not leak tasks.

**Acceptance:**

- Over SSH: `<prog-that-exits-42>; echo $?` prints 42.
- wait/waitpid on the returned pid yields exited-status 42 (not a phantom 0).
- Running the same command 50 times in one session does not exhaust task slots.

**Milestone:** M2

**Depends:** FR-SOS-036

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_spawn.spl:80, src/os/kernel/loader/fs_exec_spawn.spl:272, src/os/kernel/ipc/syscall_process.spl:145, src/os/kernel/abi/syscall_shim_process.spl:108, src/os/apps/shell/exec.spl:40

## FR-SOS-038: Distinguish Crash From Exit — a CPL3 Fault Kills Only the Faulting Task

**Goal:** A fault taken at CPL3 terminates ONLY the faulting task with a synthetic
crash status and returns control to the caller/shell, instead of iretq-looping on
the faulting instruction or taking down the kernel — so exit and crash are
observably distinct. Tightens FR-SOS-009 / FR-SOS-019; completes the M2 half of the
fault story begun in FR-SOS-028.

**Requirements:**

- The rich-fault path (`_rich_fault_entry`, which today iretq-recovers to resume)
  MUST, when the faulting frame CPL == 3, NOT resume the faulting instruction; it
  decodes vector/error/cr2/rip and routes to task termination.
- Terminate the ring-3 task with a synthetic status distinguishable from a clean
  exit (e.g. 128+vector, or a "crashed" flag), reusing the return-to-caller
  mechanism (FR-SOS-036) so the kernel and shell survive.
- Serial reports cpl, vector, faulting rip, cr2, and the task id being killed.
- CPL0 (kernel) faults keep current behavior (decode + halt/recover); only CPL3
  faults become task-scoped kills.

**Acceptance:**

- A ring-3 NULL deref emits `[fault] cpl=3 vec=14 rip=0x... cr2=0x0 task=N killed`
  exactly once (no infinite loop), the shell regains its prompt, and `$?` reports a
  crash status (nonzero, != a normal exit code).
- The kernel stays alive; a subsequent command runs in the same boot.
- A clean-exit vs a crashing program yield different `$?` classes.

**Milestone:** M2

**Depends:** FR-SOS-024, FR-SOS-036

**Anchors:** src/os/kernel/arch/x86_64/arch_init.spl:47, examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:15489, src/os/kernel/ipc/syscall_process.spl:91, src/os/kernel/loader/fs_exec_spawn.spl:272

## FR-SOS-039: Timer Tick Taken at CPL3 Is Handled and Resumes the Ring-3 Task

**Goal:** With interrupts enabled in ring 3, a timer tick taken at CPL3 is EOI'd,
the one-shot LVT re-armed, and the interrupted ring-3 task correctly resumed, so
long-running programs keep running and the kernel can regain control without
hanging or triple-faulting. Tightens FR-SOS-014.

**Requirements:**

- The ring-3 entry rflags MUST enable IF (e.g. 0x3202) — ONLY once TSS.rsp0
  (FR-SOS-024) and this handler are in place; today rflags=0x3002 (IF=0) so no
  ticks fire and a hung program is unrecoverable.
- The APIC timer LVT is one-shot; the timer ISR MUST send EOI and re-arm the
  one-shot (or switch to periodic) so ticks continue during ring-3 execution.
- The timer ISR (VEC_TIMER=32) MUST save and restore the full CPL3 iret frame
  (rip/rsp/rflags/cs/ss) so the interrupted user task resumes exactly, using the
  TSS.rsp0 stack.
- Scope is tick-survival + resume ONLY; preemptive switch-away / kill-the-hung-task
  and per-task kernel stacks are deferred to later robustness work.

**Acceptance:**

- A ring-3 loop (IF=1) produces repeated `[timer] tick cpl=3` markers and still runs
  to its own exit; the guest neither triple-faults nor hangs on the first tick.
- After a tick, a post-tick program-side marker prints, proving resume at the
  correct instruction.
- Disabling the re-arm makes ticks stop after one (regression guard).

**Milestone:** M2

**Depends:** FR-SOS-024

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_ring3.spl:361, src/os/kernel/arch/x86_64/timer.spl:116, src/os/kernel/interrupts/idt.spl:48, examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:15489

## FR-SOS-040: Fix Module-Val-Broken Image/Stack Builders So the Handoff Trusts UserProcessImage Fields

**Goal:** Root-fix the freestanding native-build module-`val` breakage so the
general `UserProcessImage` structured fields (entry, segments, initial_sp,
stack_top) and the stack_builder's SysV frame are reliable, letting the ring-3
handoff drive off the image instead of a side-channel raw blob + hardcoded literals.
Tightens FR-SOS-005.

**Requirements:**

- Fix the module-level `val` initializers that read garbage under native-build and
  force elf_loader/stack_builder/process_image (X86_64_USER_STACK_TOP,
  build_initial_stack) to be bypassed — the reason the handoff parses the ELF from
  the raw blob via mmio and ignores image fields.
- After the fix, `x86_64_fs_exec_enter_image_ring3` MUST use
  `user_process_image_entry(image)`, `user_process_image_stack_top(image)`, and
  `user_process_image_initial_sp(image)` instead of the hardcoded
  STACK_TOP=0x8000200000 and mmio-only entry.
- Once file_bytes/segments are trustworthy, drop the requirement to thread the raw
  FAT read-buffer address (blob) as a parallel channel — `image.file_bytes` must
  decode correctly under freestanding build.
- Remove the function-local-literal smoke-ordering workarounds that only exist
  because module vals read as 0/garbage.

**Acceptance:**

- `[spawn] image ... entry=0x{img_entry} builder_top=0x{builder_top} builder_sp=0x{builder_sp}`
  reports NON-ZERO builder_top/builder_sp equal to the parsed entry and chosen stack
  top (previously garbage/0).
- The proven FSEXEC.ELF reaches ring 3 using image.entry, with an assert that
  `user_process_image_entry(image)` == the mmio-parsed e_entry.
- A freestanding-config regression spec builds a UserProcessImage from bytes and
  asserts entry/segment_count/initial_sp are the real ELF values, not 0/garbage.

**Milestone:** M2

**Depends:** FR-SOS-024

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_ring3.spl:22, :276, :331, src/os/kernel/loader/x86_64_fs_exec_spawn.spl:96

## FR-SOS-041: Full SysV Auxiliary Vector in the Ring-3 Initial Stack Frame

**Goal:** Emit a complete SysV auxv (not just AT_NULL) on the ring-3 initial stack
so a real static libc `_start` (musl/glibc) initializes without faulting — most
critically AT_RANDOM for the stack canary and AT_PHDR/PHNUM/ENTRY for program
self-inspection. Tightens FR-SOS-011.

**Requirements:**

- Extend `_build_sysv_stack_frame` (today writes argc/argv/NULL/envp/NULL then only a
  single AT_NULL) to append AT_PHDR (mapped load_base + e_phoff), AT_PHENT
  (e_phentsize), AT_PHNUM (e_phnum), AT_ENTRY (e_entry), AT_PAGESZ (4096), AT_RANDOM
  (pointer to 16 initialized random bytes), AT_EXECFN (binary_path cstr),
  AT_UID/EUID/GID/EGID, terminated by AT_NULL.
- AT_RANDOM MUST point at 16 initialized bytes inside the mapped user stack; a
  missing/NULL AT_RANDOM makes glibc/musl deref 0 while seeding the canary -> #PF
  before main.
- Derive AT_PHDR/PHENT/PHNUM/ENTRY from the ELF actually mapped, with AT_PHDR from
  the same lo_page span used by `_map_pt_loads` so it addresses the in-memory phdr
  copy.
- Recompute the 16-byte rsp alignment to include the new aux pairs so argv/envp/auxv
  all land with a 16-aligned rsp at argc.

**Acceptance:**

- A musl-static "hello" ELF exec'd from the shell prints "hello" from ring 3 with no
  #PF before main.
- Serial logs each aux entry
  (`[spawn] auxv AT_PHDR=0x.. AT_PHNUM=.. AT_ENTRY=0x.. AT_RANDOM=0x..`), with
  AT_RANDOM non-zero and AT_PHDR == lo_page + e_phoff.
- A regression check reads back the frame and confirms argc, argv[0]==binary_path,
  envp NULL-terminated, and the aux array terminated by AT_NULL with required keys.

**Milestone:** M2

**Depends:** FR-SOS-024, FR-SOS-040

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_ring3.spl:97, :159, :302, :348

## FR-SOS-042: Per-Process AS Binding + User Heap Growth (brk/mmap) in the Spawned Address Space

**Goal:** Bind the freshly built per-process user address space to the
task/current-vmspace registry on ring-3 entry and seed a program break, so a real
program's brk/mmap syscalls grow demand-paged, user_rw|NX heap in its OWN address
space instead of a stale global one. Tightens FR-SOS-004.

**Requirements:**

- `x86_64_fs_exec_enter_image_ring3` MUST call `register_task_vmspace(pid, space)` and
  set the current-vmspace binding BEFORE iretq, so `_handle_brk_for_task` /
  `_handle_sys_mmap` resolve to the spawned AS instead of the stale g_current_vmspace.
- Compute a program-break base at the page above the highest mapped PT_LOAD (hi_page),
  inside the enforced user range (FR-SOS-027), and expose it through USER_BRK_BASE so
  brk(0) returns this process's correct initial break.
- brk/mmap(ANON) growth MUST map user_rw|NX demand-paged frames; the #PF handler
  (FR-SOS-028) must resolve anon faults against the REGISTERED vmspace, not stale
  global state.
- Enforce a per-process heap cap (USER_BRK_LIMIT) and fail brk/mmap growth closed
  with -ENOMEM past it.

**Acceptance:**

- A program that grows the break by N pages and writes them runs to exit(0) with no
  kernel fault markers; brk(0) returns the hi_page-aligned base.
- A program calling mmap(ANON,1 MiB), touching it, then munmap succeeds with no #PF
  in kernel space.
- M3: clang (mmap-heavy) allocates its working set in-guest with no kernel fault
  attributable to heap/AS mis-binding.

**Milestone:** M2

**Depends:** FR-SOS-027, FR-SOS-012, FR-SOS-008, FR-SOS-004 (tightens)

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_ring3.spl:305, :367, src/os/kernel/ipc/syscall_spm.spl:235, :282

## FR-SOS-043: Per-Process Address-Space Teardown + Frame Reclaim on Exit

**Goal:** Reclaim all frames of a per-process user address space on process exit so
repeated exec (shell -> command -> prompt -> next command; clang then hello) does not
monotonically leak and exhaust the PMM. Tightens FR-SOS-009.

**Requirements:**

- Add `destroy_user_address_space(space)` that walks the user AS page tables and frees
  every PT_LOAD frame, stack frame, and heap/mmap frame plus the page-table pages
  themselves, WITHOUT freeing the shared kernel-low-identity clone frames.
- On the process-exit (syscall 60) path invoke teardown for that pid's registered
  vmspace (FR-SOS-042) and unregister it; the spawn allocates each image/stack page
  and never frees them today.
- Make teardown complete/derivable from the page tables (or track per-process
  allocated frames) so no frame leaks; add a PMM free-page-count marker before/after
  exit.
- Teardown MUST switch to the kernel/next AS before freeing the exited AS's cr3 root.

**Acceptance:**

- Exec the same program K times; `[mm] free_pages before=X after=Y` shows no monotonic
  decline and no `pmm_alloc FAIL`.
- Run clang, get a prompt, then run hello; the second exec still has enough frames,
  proving the clang AS was reclaimed.
- Free-page count after a full spawn+exit returns to baseline (minus shared kernel
  frames).

**Milestone:** M2

**Depends:** FR-SOS-042, FR-SOS-009 (tightens)

**Anchors:** src/os/kernel/memory/vmm_address_space.spl:64, :23, src/os/kernel/loader/x86_64_fs_exec_ring3.spl:220, :338

## FR-SOS-044: Route SSH Remote-Exec Commands Through the Real shell_exec Pipeline (Retire REPL + Fixtures)

**Goal:** Make an SSH remote-exec command run a real ring-3 process by dispatching
through the existing `shell_exec` -> `fs_exec_spawn_ring3` -> x86_64 handoff, and
retire the SSH-side bypasses (hardcoded fixture strings and the SshRemoteShell toy
REPL) so `ssh host <cmd>` no longer returns canned bytes or "command not found" for
real binaries.

**Requirements:**

- SSHd's exec-request handler MUST, for any non-builtin command, call
  `shell_exec(cmd, argv, envp)` instead of `SshRemoteShell.feed_remote_input` (the
  generic->arch wiring itself is FR-SOS-025; this FR removes the SSH-side bypass).
- Retire the hardcoded fixture short-circuits `_ssh_exec_simple_session_line` /
  `_ssh_exec_simple_session_bytes` and `_exec_success_output_for_command` — no command
  returns canned bytes on the run path.
- `SshRemoteShell` MUST either be replaced by the shared shell or restricted to genuine
  in-process POSIX builtins; its blanket "command not found" fallback for external
  binaries MUST be removed so unknown commands go to PATH resolution + exec, and only a
  true PATH miss yields "command not found".
- argv/envp parsed from the SSH exec command line MUST be threaded through to
  `shell_exec`, not just the raw command token.

**Acceptance:**

- `ssh host /sys/apps/hello` emits `[shell-exec] exec:dispatch` / `[fs-exec] spawn:image`
  / `[spawn] entering user` markers and a real ring-3 entry, NOT
  "command not found: /sys/apps/hello".
- A source grep of the sshd exec handlers shows no remaining call to
  `_ssh_exec_simple_session_*` or `_exec_success_output_for_command` on the run path.
- `ssh host /no/such/bin` returns a PATH-miss error (rc -1) distinct from a
  spawn/load failure code.

**Milestone:** M2

**Depends:** FR-SOS-024, FR-SOS-011

**Anchors:** src/os/apps/sshd/ssh_session_channel.spl:542, :548, src/os/apps/sshd/ssh_session.spl:689, :694, src/os/apps/sshd/ssh_remote_shell.spl:39, src/os/apps/shell/exec.spl:40

## FR-SOS-045: Capture Spawned Child stdout/stderr and Real Exit Status; Deliver Over the SSH Channel

**Goal:** Capture a spawned child's stdout/stderr and its real exit code and deliver
them to the SSH client as SSH_MSG_CHANNEL_DATA (stdout) / CHANNEL_EXTENDED_DATA type 1
(stderr) plus an exit-status message, replacing the hardcoded exit_status=0 and the
REPL's in-memory output — fail-closed on spawn failure. Tightens FR-SOS-015.

**Requirements:**

- Provide a per-exec stdio sink: the ring-3 child's write(fd=1,...) and write(fd=2,...)
  syscalls land in a kernel buffer bound to the SSH channel, which the session drains
  into CHANNEL_DATA (fd1) and CHANNEL_EXTENDED_DATA code 1 (fd2).
- The SSH exit-status message MUST carry the child's real exit code (from its
  exit/exit_group syscall or scheduler wait), not a constant 0 — today
  `_finish_exec_request(_inline)` is always invoked with 0.
- Fail-closed: a negative rc from shell_exec/fs_exec MUST produce a NONZERO exit-status
  plus a diagnostic on the channel — never a phantom exit 0 with empty output.
- Ordering: all buffered stdout/stderr MUST flush to the channel before the
  exit-status / EOF / close messages.

**Acceptance:**

- `ssh host /sys/apps/hello` returns the exact bytes the child wrote to fd1 over
  CHANNEL_DATA, followed by an exit-status equal to the child's real code.
- A command writing to stderr delivers those bytes over CHANNEL_EXTENDED_DATA code 1,
  distinct from stdout.
- `ssh host /bad/path; echo $?` shows a nonzero status and the serial log shows the
  spawn-failure diagnostic; no exit-status 0 for the failed spawn.

**Milestone:** M2

**Depends:** FR-SOS-044, FR-SOS-036, FR-SOS-015 (tightens)

**Anchors:** src/os/apps/sshd/ssh_session_channel.spl:564, :539, src/os/apps/sshd/ssh_session.spl:748, src/os/apps/sshd/ssh_remote_shell.spl:34, src/os/kernel/loader/x86_64_fs_exec_ring3.spl:270

## FR-SOS-046: Bake a libc-Linked hello ELF as the M2 Return-to-Shell Artifact

**Goal:** Produce and bake a real libc-linked hello program (crt0.o +
libsimpleos_c.a, statically linked, no PT_INTERP) at a shell-resolvable path, giving
M2 an artifact that exercises the full runtime startup frame and return-to-shell,
distinct from the M1 syscall-only freestanding ELF. Tightens FR-SOS-011.

**Requirements:**

- Add a build recipe that links a hello source against `build/os/sysroot/lib/crt0.o`
  and `libsimpleos_c.a` (NOT -nostdlib -ffreestanding) producing a static
  x86_64-unknown-simpleos ELF at `build/os/user_hello/hello_libc.elf`.
- Assert the artifact statically links, has crt0 `_start` as entry, at least one
  PT_LOAD, and no PT_INTERP; record size.
- Bake it at `/usr/bin/hello` (or `/usr/bin/hello_libc`) so `shell_path_search`
  resolves it, and confirm coherence via the FR-SOS-030 validator.
- The runtime frame (argv/envp/auxv + stdio before main) and
  process-exit->scheduler-resume-shell are consumed from FR-SOS-041 / FR-SOS-036, not
  re-implemented here.

**Acceptance:**

- Host: readelf shows statically linked, crt0 `_start` entry, PT_LOAD present, no
  PT_INTERP; nm shows main + libsimpleos_c symbols.
- The FR-SOS-030 validator confirms the libc hello bytes are coherent at its guest
  path.
- QEMU: running the libc hello from the shell prints its stdout AND the shell prompt
  returns (observable as program-output followed by a fresh prompt marker).

**Milestone:** M2

**Depends:** FR-SOS-036, FR-SOS-041, FR-SOS-011 (tightens)

**Anchors:** scripts/os/build_user_hello_elf.shs:21, build/os/sysroot/lib/crt0.o, build/os/sysroot/lib/libsimpleos_c.a, src/os/port/disk_image_bake.spl:182

## FR-SOS-047: Return-to-Shell Acceptance — Process Exit Resumes the Scheduler and the Prompt Returns

**Goal:** Prove that after a spawned process exits, control returns to the shell via
scheduler resume and a fresh prompt appears, rather than the single-shot behavior
where the handoff iretqs and then exits QEMU via `out 0xf4` on first process exit. The
harness MUST NOT accept single-shot exec as the M2 end state. Tightens FR-SOS-009.

**Requirements:**

- Run two sequential commands from the shell within one boot; assert serial shows
  launch#1, PROC_EXIT(code#1), a SHELL_PROMPT_READY marker, launch#2, PROC_EXIT(code#2).
- QEMU MUST exit only after the shell session completes, not on the first process exit;
  a machine-exit on first PROC_EXIT classifies RED.
- Assert per-process exit codes are captured distinctly (proving scheduler resume, not a
  fresh boot).
- Add the SHELL_PROMPT_READY / prompt-return marker to the serial contract so the
  ordering is greppable.

**Acceptance:**

- Serial contains the ordered markers launch#1 -> PROC_EXIT code#1 -> SHELL_PROMPT_READY
  -> launch#2 -> PROC_EXIT code#2.
- Single-shot behavior (QEMU dies on first process exit) yields RED.
- Exit codes for the two commands are observed independently on serial.

**Milestone:** M2

**Depends:** FR-SOS-032, FR-SOS-033, FR-SOS-036

**Anchors:** src/os/kernel/loader/x86_64_fs_exec_ring3.spl:367, examples/09_embedded/simple_os/arch/x86_64/fs_exec_general_ring3_entry.spl:25, src/os/apps/shell/exec.spl:40

## FR-SOS-048: clang Size-Reduction to Floor + On-Disk Budget Contract + Fail-Closed Bake Gate

**Goal:** Given clang_static is ~119MB and cannot fit the guest's on-disk whole-file
read budget, minimize the clang artifact to its practical floor, define an explicit
on-disk-exec size-budget contract, and enforce a fail-closed host gate that verifies
size and ELF format before the toolchain bake proceeds (today
`guest_toolchain_execution_gate` only checks file existence).

**Requirements:**

- Add a size-reduction pass to the clang_static relink (llvm-strip of debug/symbols,
  `-Wl,--gc-sections`, and evaluate a clang `-cc1` / thin-driver-only subset) and record
  the measured floor; do NOT claim a 4MiB target — a static clang floor is ~100MB, so
  the contract is "artifact <= declared_budget", not a fixed 4MiB.
- Define a single declared on-disk-exec budget value shared by the bake and the guest
  reader; the baked clang size is measured against and gated by this budget.
- Extend `guest_toolchain_execution_gate` (existence-only today) to also assert
  clang_static has no PT_INTERP, entry == simpleos.ld base (0x10000000), is statically
  linked, and size <= declared_budget — failing closed (nonzero, bake aborts) otherwise.
- Growing the guest read buffer (`simpleos_fat32_path_read_buf[4194304]` /
  FAT32_PATH_READ_BUFFER_MAX) to the declared budget is a reader/boot dependency
  (FR-SOS-020/023), referenced here, not re-specified.

**Acceptance:**

- Host: the gate exits nonzero and the bake does NOT run when clang_static size >
  declared_budget or when it carries a PT_INTERP; exits 0 only when both format and size
  checks pass.
- Host: stripped/gc-sections clang measured size is emitted and is materially smaller
  than the 119MB baseline.
- QEMU (deferred, depends on reader-buffer growth): with the budget grown to the clang
  floor, booting the clang image runs clang --version / -cc1 in-guest and serial shows
  the clang version banner.

**Milestone:** M3

**Depends:** FR-SOS-020, FR-SOS-023

**Anchors:** examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:2655, :2793, src/os/port/llvm/clang_static.shs:1, src/os/port/guest_toolchain_execution_gate.spl:1, src/os/port/disk_image_bake.spl:224

## FR-SOS-049: Decouple the rust Artifact From the clang Toolchain Bake Gate

**Goal:** Ensure enabling the toolchain bake to embed the goal-critical clang does not
hard-fail on the absent rustc_static (which has no build recipe — only clang_static.shs
exists), by decoupling rust from the shared toolchain marker or providing a rustc_static
relink recipe mirroring clang_static.shs.

**Requirements:**

- Today `build/os/.bake_include_toolchain` causes `disk_image_bake` to return Err when
  `build/os/rust_static/bin/rustc_static` is missing, blocking the clang bake; split the
  marker (or add a clang-only path) so clang bakes independently of rust.
- If rust is retained, provide a rustc_static static-relink recipe mirroring
  `clang_static.shs` (static, -no-pie, -nostdlib, -T simpleos.ld, no PT_INTERP, entry at
  simpleos.ld base) gated behind its own marker with the same FR-SOS-048-style
  format+size validation.
- rust is in no milestone definition (the goal is clang builds+runs hello); its bake MUST
  be optional and non-blocking for the clang/hello path.

**Acceptance:**

- Host: with only clang_static present (no rustc_static) and a clang-only marker set, the
  bake completes and embeds clang without a "rustc_static missing" Err.
- Host: when the rust marker is set, either a rustc_static recipe produces a static
  no-PT_INTERP ELF that passes the gate, or the bake reports rust as skipped/optional
  without failing the clang path.
- No regression: the existing combined toolchain bake still works when both artifacts are
  present.

**Milestone:** M3

**Depends:** FR-SOS-048

**Anchors:** src/os/port/disk_image_bake.spl:246, :187, :226, src/os/port/llvm/clang_static.shs:1

## FR-SOS-050: End-to-End Over SSH — clang Builds hello In-Guest and the Arbitrary-Path Binary Runs

**Goal:** Prove the end goal over SSH: build hello with clang and run the freshly-built
binary from an arbitrary filesystem path, with its stdout streamed back to the client and
exit 0 — a general OS that runs any FS executable, not only registered `/sys/apps`
entries. SSH login/auth is already proven; this is the capstone. Tightens FR-SOS-017.
Merges the shell-ssh capability and the verify acceptance-harness requests.

**Requirements:**

- The shell MUST exec an arbitrary absolute path produced at runtime by clang (e.g.
  `/tmp/hello`), not only registry-seeded `/sys/apps/<name>` (registration-free
  resolution is FR-SOS-021, consumed here end-to-end).
- The full SSH pipeline (real exec + channel-captured stdout/exit + return-to-shell) MUST
  operate for a program the OS never saw before boot.
- Layered acceptance: case 1 runs a baked hello ELF over SSH returning stdout
  "hello, world" + exit 0 (a hardcoded-fixture response is RED); case 2 (capstone) is a
  single invocation `clang -o /tmp/hello /root/hello.c && /tmp/hello` (or two sequential
  commands) that builds then runs, streaming stdout back and returning exit 0.
- Record the clang binary size budget (~119MB vs the on-disk budget) as a gating
  diagnostic so a busted image is visible, not silently passed.
- Fail-closed: if the build fails the run MUST NOT execute and the client sees the
  compiler's nonzero status; if the built binary faults the client sees a nonzero status
  plus fault decode, never phantom success. The harness is self-terminating with a bounded
  timeout; a REPL hang or unanswered channel is RED.

**Acceptance:**

- `ssh host 'clang -o /tmp/hello /root/hello.c && /tmp/hello'` prints hello's stdout on
  the SSH channel and returns exit-status 0, asserted distinct from the fixture strings.
- Running the same `/tmp/hello` a second time in the session still works and the prompt
  returns.
- No part of the run relies on `_ssh_exec_simple_session_*` fixtures or a pre-registered
  app entry for `/tmp/hello`; a canned-fixture or channel hang classifies RED.

**Milestone:** M3

**Depends:** FR-SOS-044, FR-SOS-045, FR-SOS-047, FR-SOS-021, FR-SOS-048, FR-SOS-013, FR-SOS-017 (tightens)

**Anchors:** src/os/apps/sshd/ssh_session_channel.spl:526, src/os/apps/shell/exec.spl:31, src/os/services/vfs/vfs_boot_init.spl:696, :738, src/os/_QemuRunner/scenario_exec.spl:652, test/03_system/os/qemu/sys_qemu_x86_64_fs_exec_spec.spl:39
