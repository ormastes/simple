# SOSIX POSIX-compatibility interface V1

Date: 2026-09-26. Status: interface definition + vertical slices 1 (uname),
2 (stdio), 3 (mmap arena), and 4 (termios). SimpleOS program roadmap point
2. AArch64 lanes only; no x86 surface is defined or implied by this
document.

SOSIX is the SimpleOS POSIX-compatibility interface layer: the contract that
lets FreeBSD-style userland sources (and clang's runtime expectations) target
SimpleOS without per-program shims. It has three owners:

- **Interface constants + identity** — `src/os/services/sosix/interface_v1.spl`
- **Kernel handlers** — versioned modules under `src/os/services/sosix/`,
  dispatched from `src/os/kernel/ipc/syscall.spl` and exported to the C boot
  layer as optional strong shims (`src/os/kernel/abi/syscall_shim_sosix.spl`)
- **Guest libc** — `src/os/libc/` (POSIX facades over the raw ids; owns
  `errno`, `strerror`, stdio, malloc)

Prior art this extends (do not fork): `src/os/sosix/` (process, fs positioned
IO 134/135, dataset/queue sharing 120-131, host adapters),
`doc/05_design/os/sosix_execve_vectors_v1.md` (execve vector ABI),
`src/os/posix/` (errno facade re-exporting `os.kernel.errno`).

## 1. Syscall-id map

One id space, assigned in `src/os/kernel/ipc/syscall.spl::syscall_handler`.
Status legend: **wired** = handler implemented and reachable from a live trap
path; **partial** = reachable with documented semantic gaps; **absent** = id
reserved, returns -ENOSYS. "POSIX name" is the SOSIX-facing name; ids marked
(non-POSIX) are SimpleOS-native extensions a ported program must not call.

| id | POSIX name | Signature (arg0..arg4) | Status |
|----|-----------|------------------------|--------|
| 0 | `exit` | status, -, -, -, - | wired |
| 1 | (non-POSIX) `yield` | - | wired |
| 2 | (non-POSIX) `spawn` | - | wired |
| 3 | (non-POSIX) `wait` | - | wired |
| 4 | `getpid` | - | wired |
| 5 | (non-POSIX) `list_tasks` | - | wired |
| 6 | (non-POSIX) `get_task_info` | - | wired |
| 7 | `kill`-family `signal` | pid, sig, -, -, - | wired |
| 8 | (non-POSIX) `set_priority` | - | wired |
| 9 | (non-POSIX) `get_parent_pid` | - | wired |
| 10 | `mmap` (anonymous) | hint, len, prot, flags, - | partial (anon-only; free-list arena `mmap_v1` landed + host-verified, but the arm64 guest still dispatches to the bump arena — case-arm flip pending) |
| 11 | `munmap` | addr, len, -, -, - | partial (arena `release` frees + coalesces host-side; no-op on the arm64 guest's bump path) |
| 12 | `mprotect` | addr, len, prot, -, - | partial (arena `protect` flips perms host-side; arm64 guest unchanged) |
| 13 | (non-POSIX) `spawn_binary` | - | wired |
| 14 | (non-POSIX) `enter_user_blocking` | - | partial |
| 15 | `brk` | addr, -, -, -, - | wired |
| 16 | (non-POSIX) `system_reboot` | - | wired |
| 17 | reserved | - | absent |
| 18-23 | (non-POSIX) IPC port/endpoint | - | wired |
| 24-29 | (non-POSIX) notification | - | wired |
| 30 | `open` | path, pathlen, flags, mode, - | wired (gap: the guest C-ABI byte-slice open extern does not plumb the `mode` argument — create perms default in the kernel; recorded by the stdio slice) |
| 31 | `read` | fd, buf, count, -, - | wired |
| 32 | `write` | fd, buf, count, -, - | wired |
| 33 | `close` | fd, -, -, -, - | wired |
| 34 | `stat`/`fstat` | path, pathlen, buf, form, - | wired |
| 35 | `mkdir` | path, len, mode, -, - | wired |
| 36 | `readdir` (opendir/readdir facade) | fd, entry, -, -, - | wired |
| 37/38 | (non-POSIX) `mount`/`unmount` | - | wired |
| 39 | `unlink` | path, len, -, -, - | wired |
| 40/41 | (non-POSIX) `pledge`/`unveil` | - | wired |
| 42/49 | (non-POSIX) capability grant/revoke | - | wired |
| 43 | `ftruncate` | fd, len, -, -, - | wired |
| 44 | `rename` | old, oldlen, new, newlen, - | wired |
| 45 | `rmdir` | path, len, -, -, - | wired |
| 46 | `lseek` | fd, offset, whence, -, - | wired |
| 47 | `getcwd` | buf, size, -, -, - | wired |
| 48 | `chdir` | path, len, -, -, - | wired |
| 50 | `clock_gettime` | clock_id, ts*, -, -, - | wired (0=REALTIME, 1=MONOTONIC) |
| 51 | (non-POSIX) `sleep` (ns; `nanosleep` facade in libc) | ns, -, -, -, - | wired |
| 52-56 | reserved | - | absent |
| 57 | `fork` | - | wired |
| 59 | `execve` | path, pathlen, argv*, envp*, 0 | wired (5-arg vector ABI, sosix_execve_vectors_v1) |
| 60 | (non-POSIX) `debug_write` | char, -, -, -, - | wired |
| 61 | `waitpid` | pid, -, options, -, - | wired |
| 62 | `pipe` | fds*, -, -, -, - | wired |
| 63/64 | `dup2`/`dup` | oldfd, newfd, -, -, - | wired |
| 65-67 | (non-POSIX) `dlopen`/`dlsym`/`dlclose` | - | wired |
| 68 | `poll` | fds*, nfds, timeout, -, - | wired |
| 69 | `fcntl` | fd, cmd, arg, -, - | wired (F_SIMPLEOS_GET_OFD available; stdio_v1 does not consume it — one FILE per fd is the supported shape, see §6) |
| 70-77 | socket family `socket`..`ifconfig` | - | partial (arm64: virtio-net path only) |
| 78 | `fsync` | fd, -, -, -, - | wired |
| 79 | (non-POSIX) dbfs mount capability | - | wired |
| 80-87 | (non-POSIX) device enumerate/grant/BAR/DMA | - | wired (kernel-only from ring-3: -EPERM) |
| 88/89 | reserved | - | absent |
| 90/91 | (non-POSIX) kernel log write/read | - | wired |
| **92** | **`uname`** | **utsname_buf\*, -, -, -, -** | **wired (this slice; SOSIX_SYS_UNAME)** |
| 93/94 | reserved | - | absent |
| 95 | (non-POSIX) `sysinfo` | kind, -, -, -, - | wired |
| 96/97 | (non-POSIX) `get_hostname`/`set_hostname` | - | wired |
| 98 | (non-POSIX) `privctl` | - | wired |
| 99-102 | (non-POSIX) memory grant/revoke/safecopy | - | wired |
| 103/104 | `mmap`/`munmap` (VM syscall form) | addr, len, prot, flags, fd | wired |
| 105 | reserved | - | absent |
| 106/107 | (non-POSIX) schedule/schedctl | - | wired |
| 108/109 | reserved | - | absent |
| 110-115 | (non-POSIX) SPM privilege/window/approval | - | wired |
| 116 | (non-POSIX) startup-evidence consume | - | wired |
| 117-119 | reserved | - | absent |
| 120-131 | (non-POSIX) SOSIX dataset/queue sharing | - | wired |
| 132/133 | reserved | - | absent |
| 134/135 | (non-POSIX) SOSIX positioned pread/pwrite (registered buffers) | - | wired |

Guest-libc usage today (lane-C1/R4 analysis, `src/os/libc/simpleos_libc.c`,
`simpleos_fs.c`, arm64 C dispatch in `baremetal_stubs.c`): ids
0, 4, 10-12, 30-36, 39, 43-48, 50, 60, 69. New SOSIX ids must be allocated
from the reserved holes above and recorded here in the same change.

## 2. Errno conventions

- Kernel handlers return **negated errno** in `SyscallResult.value`
  (e.g. `-22` EINVAL, `-14` EFAULT, `-38` ENOSYS). Zero/positive is success.
- The numeric ABI is owned by **`os.kernel.errno`** (`src/os/kernel/errno.spl`);
  `os.posix.errno` re-exports it, and the guest `<errno.h>`
  (`src/os/libc/include/errno.h`) mirrors the same numbers. All three move
  together; never hardcode an errno number in a fourth place.
- The guest libc owns the user-visible `errno` variable and `strerror()`
  prose (`src/os/libc/simpleos_string_ext.c`). The kernel-side symbolic
  table is `sosix_errno_name_v1` (`src/os/services/sosix/errno_text_v1.spl`).
- Unknown syscalls return `-38` (-ENOSYS), including unassigned reserved ids.

## 3. Path, fd, and open-file-description model

- **Paths**: NUL-terminated byte strings, at most 256 bytes
  (`MAX_BINARY_PATH_LEN`, `src/os/kernel/ipc/syscall.spl`). Syscalls take
  `(pointer, length)` pairs, not NUL-terminated reads, on every path arg.
  UTF-8 only; embedded NUL and invalid UTF-8 yield -EINVAL.
- **File descriptors**: small per-task integers owned by the kernel fd table
  (`os.kernel.fd_table`; `fd_activate_task` on dispatch). 0/1/2 are the stdio
  fds. `dup`/`dup2`/`pipe`/`close` operate on caller-owned fds only.
- **Open file descriptions (OFD)**: the cursor/status object behind an fd.
  `fcntl(fd, F_SIMPLEOS_GET_OFD, ...)` (id 69) exposes the guest-visible OFD
  identity so stdio can share cursors across duplicated fds. SOSIX positioned
  IO (ids 134/135) bypasses the shared cursor by explicit offset and requires
  registered buffers (`src/os/sosix/fs/`).
- **VFS routing**: kernel file syscalls route to the VFS service over IPC;
  the arm64 clang-bringup kernel instead serves them from the C layer
  (`arm64_svc_file_*` in `baremetal_stubs.c`) because the Simple strong-shim
  path parks the guest. Both are the same ids and semantics.

## 4. Compatibility contract for FreeBSD-style sources

A ported POSIX.1-2017 program may assume the following subset. Anything not
listed here is not SOSIX V1 and must be probed or avoided.

- **File IO**: open/read/write/close/lseek/ftruncate/fsync, stat/fstat,
  mkdir/rmdir/unlink/rename, getcwd/chdir, opendir/readdir facade, pipe,
  dup/dup2, poll, fcntl (OFD query). Wired ids per §1.
- **stdio**: the SOSIX FILE* surface lives in
  `src/os/services/sosix/stdio_v1.spl` (vertical 2, roadmap item 1): fopen/fdopen/fclose/fflush,
  fread/fwrite/fgets/fgetc/fputc/fseek/ftell/rewind/feof/ferror/clearerr/
  setvbuf/fileno over an injected ops vtable (ids 30-33/46; no kernel changes),
  with stdin/stdout/stderr pre-opened on fds 0/1/2 (stdout line-buffered
  unconditionally, stderr unbuffered, stdin line-buffered input; the isatty
  probe into this buffering is the documented follow-up in §6, not the
  termios slice). `stdio_v1_guest.spl` wires the vtable to the raw ids with
  the DebugWrite (id 60) console fallback. The guest toolchain's C stdio
  remains the lane-C1 sysroot's `libsimpleos_c.a`, not the kernel.
- **termios**: the SOSIX terminal-attribute surface lives in
  `src/os/services/sosix/termios_v1.spl` (vertical 4, roadmap item 2):
  tcgetattr/tcsetattr (TCSANOW/TCSADRAIN/TCSAFLUSH), isatty(fd) (true
  exactly for fds 0/1/2, the serial console), tcdrain/tcflush/tcflow
  (backend hooks; honest no-ops on today's guest), and
  cfget/cfset{ispeed,ospeed} (store-and-return — the serial driver sets
  baud at init), over an injected drain/flush_input ops vtable (no kernel
  changes). Every constant mirrors the guest `<termios.h>` numeric ABI
  (NCCS=32, flag bits, B0..B115200); ICANON/VMIN/VTIME are implemented as
  the pure read-size policy `sosix_termios_read_size_v1`, while ECHO/ISIG/
  ONLCR and the remaining flags are stored but not enforced (no
  line-discipline owner exists yet — see the module doc's flag-by-flag
  contract). The guest C facades (`src/os/libc/simpleos_termios.c`) keep
  their ENOSYS fail-closed stance until a kernel tty path exists.
- **malloc**: guest libc dlmalloc arena over anonymous `mmap` (id 10); the
  arm64 heap is still the bump arena on the live dispatch path — the
  free-list arena (vertical 3) replaces it when the id-10 case arm flips.
- **string**: guest libc string/memory functions (no kernel involvement).
- **mmap**: anonymous, private mappings only; `MAP_FIXED` honored only inside
  the user window; file-backed mappings are a later slice. Semantics per the
  vertical-3 arena (`src/os/services/sosix/mmap_v1.spl`): first-fit at the
  lowest address (bump-compatible growth), munmap frees + boundary-tag
  coalesces (idempotent; unmapped pages in the range are skipped), mprotect
  is all-or-nothing (-EFAULT on any unmapped page), msync is a no-op success
  (no file-backed writeback yet).
- **clock**: `clock_gettime` id 50 (CLOCK_REALTIME from RTC, CLOCK_MONOTONIC
  from the scheduler tick); `nanosleep` facade over id 51.
- **uname**: id 92, `struct utsname` = 5 fields × 65 bytes
  (`_UTSNAME_LENGTH`), NUL-padded. This slice's vertical.
- **exec**: `execve` id 59 with the five-argument vector ABI and the bounds
  of `sosix_execve_vectors_v1` (64 argv / 128 envp slots incl. NULL, 256-byte
  path, 4096-byte strings, 32768-byte per-vector budget).

## 5. OS identity (uname) contract

`uname` (id 92) fills, per roadmap point 3:

| field | value | source |
|-------|-------|--------|
| sysname | `SimpleOS` | constant `SOSIX_UTSNAME_SYSNAME` (MUST NOT change) |
| nodename | `simpleos` (FreeBSD-like node name; settable via id 97) | `SOSIX_UTSNAME_NODENAME` |
| release | `1.0.0` — FreeBSD-like `release` field | `os.packages.os_packages.os_version()` |
| version | `SimpleOS 1.0.0 sosix-1` | `os_version()` + `SOSIX_INTERFACE_VERSION` |
| machine | `aarch64` on arm64 lanes | arch constant |

The guest libc keeps its local `uname()` (`src/os/libc/simpleos_utsname.c`)
as the portable fallback; the syscall is the canonical source once the C
dispatch routes id 92 to the strong shim `spl_handle_uname`.

## 6. Delivered verticals and next slices

Delivered as V1 vertical 1 (uname): interface constants (`interface_v1.spl`),
the uname handler (`uname_v1.spl`), the kernel errno-name table
(`errno_text_v1.spl`), dispatch case 92 (`syscall.spl`), and the optional
C-ABI shim (`syscall_shim_sosix.spl` + hub registration).

Delivered as V1 vertical 2 (stdio, roadmap item 1): the SOSIX FILE* surface
(`stdio_v1.spl`) — fopen/fdopen/fclose/fflush, fread/fwrite/fgets/fgetc/
fputc/fseek/ftell/rewind/feof/ferror/clearerr/setvbuf/fileno over an
injected ops vtable (ids 30-33/46 only; no kernel changes), plus
`stdio_v1_guest.spl` wiring the vtable to the raw ids with the DebugWrite
(id 60) console fallback for fd 1/2. Buffering contract: files fully
buffered (4096 default), stdin line-buffered input, stdout line-buffered
unconditionally (no tty to probe), stderr unbuffered. Host-side spec:
`test/01_unit/os/services/sosix_stdio_v1_spec.spl` (25 examples over a
fake backend). Gaps recorded in the §1 status column: id 30's `mode` arg
is not plumbed through the guest C-ABI open extern; id 69
(F_SIMPLEOS_GET_OFD) is not consumed — two FILEs on dup'd fds sharing one
kernel cursor stay POSIX-undefined (one FILE per fd is the supported
shape).

Delivered as V1 vertical 3 (mmap semantics, roadmap item 2 first half): the
per-guest-address-space boundary-tag free-list arena
(`src/os/services/sosix/mmap_v1.spl`) with an injected page-source vtable
(no kernel imports — host-testable), the kernel-side owner
(`src/os/kernel/memory/sosix_mmap_v1.spl`: VMM/PMM-backed ops with the W^X
parity rule + SyscallResult-shaped handlers for the id-10 family), and the
host-side spec `test/01_unit/os/services/sosix_mmap_v1_spec.spl` (21
examples: alloc/split/reuse/coalesce, munmap-then-remap-same-span, hint +
MAP_FIXED, mprotect flips + EFAULT all-or-nothing, msync no-op, ENOMEM
rollback, invariant walker over I1-I4). NOT YET WIRED: both id-10 case
arms (the Simple-kernel `case 10/11/12` in `syscall.spl` →
`_handle_memory_map`, and the R4 lane's C `case 10` → `arm64_user_mmap` in
`baremetal_stubs.c`) still run the legacy bump paths; flipping them is one
line per arm plus per-AS arena instantiation at launch, gated on the R4
lane's QEMU boot cycle. No R4-owned file was touched by this slice.

Delivered as V1 vertical 4 (termios, roadmap item 2): the SOSIX
terminal-attribute surface (`src/os/services/sosix/termios_v1.spl`) —
tcgetattr/tcsetattr (TCSANOW/TCSADRAIN/TCSAFLUSH discipline over the
injected drain/flush_input hooks), isatty(fd) (true exactly for fds
0/1/2, the serial console; dup'd console fds unrecognized in v1),
tcdrain/tcflush/tcflow (honest no-ops on today's guest, rationale in the
module doc), cfget/cfset{ispeed,ospeed} (store-and-return; the PL011
driver sets 115200 at init), and the pure ICANON/VMIN/VTIME read-size
policy `sosix_termios_read_size_v1` — all over the
`SosixTermiosOpsV1` vtable with no kernel imports, numeric ABI in parity
with the guest `<termios.h>` (NCCS=32, flag bits, B0..B115200). Flag
honesty: ICANON/VMIN/VTIME drive the read policy; ECHO/ECHOE/ECHOK/ECHONL/
ISIG/ONLCR/OPOST/c_iflag/c_cflag are stored but not enforced (no
line-discipline owner exists yet). Host-side spec:
`test/01_unit/os/services/sosix_termios_v1_spec.spl` (28 examples over a
fake console backend). No syscall ids consumed; stdio_v1's unconditional
stdout line-buffering intentionally stays as-is this slice.

Recommended next slices, in order:

1. **mmap case-arm flip + file-backed `mmap`** — wire the verified arena
   into the id-10 family on the arm64 guest (one-line case arms + per-AS
   arena at launch; R4's QEMU cycle is the gate), then file-backed
   mappings (VFS read into the page source at map fault or map time).
2. **stdio isatty probe** — stdio_v1 keeps its unconditional stdout
   line-buffering (the termios slice deliberately did not touch it);
   once a guest wires termios, probe `isatty(1)` so redirected stdout
   becomes fully buffered (clang's driver probes `isatty(1)` for color
   diagnostics — that probe now has an honest answer).
3. **Kernel tty path** — a tty/input-queue syscall family plus
   `termios_v1_guest.spl` (replacing the two honest no-op hooks), the
   line-discipline owner that enforces ECHO/ISIG/ONLCR, and rewiring the
   guest C termios facades off their ENOSYS fail-closed stance.
4. Routing id 92 in the arm64 C dispatch
   (`arm64_dispatch_optional_shim(spl_handle_uname, ...)` — one line, owned by
   the clang-bringup lane) once the strong-shim guest-park issue documented in
   `baremetal_stubs.c` no longer applies to this path.
5. OFD-aware stdio coordination (id 69): let a second FILE on a dup'd fd
   detect the shared cursor instead of silently double-buffering it.
