# UP2 ring-0 image retains hosted SimpleOS syscall trampoline

Status: RESOLVED (2026-08-20) — freestanding kernel boots and runs VFS `ls /`
Owner: UP Squared Apollo Lake SimpleOS lane
Date: 2026-08-20

OVMF now reaches the ELF32 shim, `_entry32`, and 64-bit kernel entry. The next
fault is exactly `simpleos_syscall`'s `syscall` instruction at ring 0, first
during a module initializer allocation and then during Simple entry execution.
The kernel must not install a fake hosted syscall ABI to hide this fault.

Initial root cause evidence:

- pure Simple core calls standard C primitives such as `memcpy`;
- `src/os/libc/simpleos_libc.o` previously had one monolithic `.text` section;
- resolving one live primitive retained the same section's userspace
  `write/open/exit` implementations;
- those functions retain `simpleos_syscall`, even though they are dead for the
  board entry; and
- the linker already uses `--gc-sections`, but cannot collect individual
  functions inside that monolithic section.

Those changes reduced the retained image, but the next build proved they are
not sufficient. The selected `x86_64-unknown-simpleos` native target is a
filesystem-launched userspace lane. Its generated `_start` calls `exit`, and
the retained pure-core diagnostic paths call `write`; both resolve through the
hosted libc syscall trampoline. The UP2 image therefore still fails its new
`simpleos_syscall` absence gate.

The checkpoint adds `-ffunction-sections -fdata-sections` to the x86 libc
Makefile, makes Makefile changes invalidate its objects, refreshes the admitted
libc archive during the UP2 build, limits native-runtime import to port I/O,
and supplies board freestanding allocation/string/serial primitives. These
changes are retained as useful isolation work, but they do not close this bug.

Resolution: the implementation uses the existing `x86_64-unknown-none`
freestanding kernel link lane, which does not synthesize the SimpleOS userspace
`_start`. The admitted compiler emits the Simple closure as an archive; the
board wrapper directly links it with the board-owned Multiboot CRT and
freestanding runtime capsule. A board-owned `write` implementation sends only
stdout/stderr bytes to COM1 and rejects other descriptors.

The final 37,280-byte ELF has entry `0x08000038`, binds `spl_start` to the
UP2 Simple entry, and has no `simpleos_syscall`. Its exact 256 MiB removable
image passed the structural checker and `--ovmf`: loader admission, ELF32 shim,
32/64-bit entries, ordered kernel markers, and a freshly injected `ls /` whose
VFS window contains `/bin`, `/etc`, and `/README.txt`. Physical board evidence
remains separate.
