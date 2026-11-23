# Windows cross-link import stubs prevent bounded child launch

Status: open; repair verification pending.

The Windows native compiler produced by workflow 45254122525 at
d3422d488768713c1e6153bd2a7766ff22cbbd23 starts successfully but cannot complete
the installed-memory query at the beginning of native-build. Standard ladder
verification 45269778636 timed out after 900 seconds with no compiler phase output.
The outer Job governor reported exit 124 and quiescent=1. This is not a memory-cap
failure: peak RSS was 29,500 KiB.

The compiler used 889.25 CPU seconds over 892.2 seconds while its PowerShell
TotalVisibleMemorySize child used zero CPU. The call requests a 20,000 ms bound.
Disassembly identifies the first concrete defect: Thread32First and Thread32Next
are local `mov eax,3; ret` definitions. They never populate THREADENTRY32.
The selected Rust runtime's process_bytes_windows::resume_primary therefore
loops before resuming the child or entering the timed capture loop.

The bootstrap stub generator emitted 62 functions, explicitly including these
ToolHelp APIs and PeekNamedPipe. Its existing target import-library resolver
was restricted by a Windows **host** cfg. The Linux-to-Windows link instead
passed an empty system-library inventory, so incomplete static name heuristics
allowed real OS APIs to become return-3 bootstrap definitions. Explicit object
definitions then won over genuine archive import thunks.

Repair: use the existing final-link library inventory on Windows GNU target
links from other hosts. Preserve optional Clang target flags (target-prefixed
GCC needs none), explicit search directories, and reject unsuccessful driver
queries. Do not add fabricated API bodies or bypass the memory query.

Focused acceptance is actual Clang and GNU import discovery, preservation of
an intentional local-symbol negative control, failure-status rejection,
genuine ToolHelp imports in the emitted PE, and real retained-runtime process
completion plus inner timeout and child quiescence. A successful helper does
not qualify the original compiler or erase its two failed Hello invocations.
Compiler-level qualification remains separate; no additional full compiler
build is part of the focused regression.

Producer SHA256:
`a60b9ff3aa41e5ada5a1884a3f729791f4576518f996ba8b4d3f55bc463db446`.
Matching native-runtime SHA256:
`7fc91928c1ff216caa45375f62aff87c174b31a6893f8ea21ff9b544ad1e40f9`.
