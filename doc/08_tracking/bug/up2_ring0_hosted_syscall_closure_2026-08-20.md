# UP2 ring-0 image retains hosted SimpleOS syscall trampoline

Status: OPEN — build gate added; kernel link lane still unresolved
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

The next implementation must select or add a genuine x86_64 freestanding
kernel link lane that does not synthesize the SimpleOS userspace `_start` and
does not silently pull the generic legacy boot closure over the board-owned
Multiboot entry. Then rebuild once and require
`hosted_syscall_symbols=0`, boot that exact image under OVMF, and require the
ordered UP2 markers plus command-correlated `ls /` output. Physical board
evidence remains separate.
