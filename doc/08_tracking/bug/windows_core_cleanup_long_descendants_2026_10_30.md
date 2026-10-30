# Windows core cleanup fails on long descendants

The owned31 SSpec attempt ended after 109,022 ms with native compiler exit -1,
`limit=infrastructure`, `budget=pass`, `completion=unavailable`, followed by
`NATIVE-CACHE-CLEANUP-FAILED`. Its outer receipt recorded exit 1, peak RSS
5,926,240 KiB below the 7,340,032 KiB cap, and no abnormal NTSTATUS. Neither
the 900-second test deadline nor the 1,200-second outer deadline expired.
The shard headroom warning alone does not establish a memory failure.

Retained child scope paths reach 350 characters; a native-cache reverse-reference
receipt path is 304 characters. LLDB loaded the actual runner and PDB (runner
SHA256 `e101710a6ccd629e5c77f42b962729d6ee33ced6b100e77b6efc8ab329e8de9c`)
and resolved `rt_dir_remove_all` at `0x140275a40`; its helper at `0x140275ae0`
calls `GetFileAttributesA`. The old core implementation used ANSI enumeration
and deletion without an extended path prefix. An isolated exact-function
330-character descendant fixture failed with Win32 error 145 (directory not
empty). Original failed-attempt artifacts were not removed or rerun.

Core and full Windows cleanup now share `runtime_win_remove_tree.h`. It converts
UTF-8 to UTF-16 and prefixes the absolute root even when that root is short:
appended descendants can exceed MAX_PATH. Recursive entries remove reparse
points themselves without traversing their targets. Enumeration errors and
deletion failures remain failures. Existing missing-path policy remains core
success versus full-runtime failure; core file removal remains supported.

Validation: `python scripts/check/check-windows-remove-tree.py --cc <Windows-GNU-clang>
--work-dir <new-private-directory>` passes eight cases linked with eight actual
production core-C owners and eight cases using the shared full-runtime policy:
normal trees, Unicode, descendants over 350 characters, missing paths,
junctions and file symlinks preserving an outside sentinel, trailing separators,
and read-only deletion refusal. A negative control linking the original core
owner with the same seven production companions refuses the long-path fixture.
The full platform owner is syntax-compiled; its broad runtime link is not
qualified by this fixture. Original-wrapper diagnostics can mask the cleanup
cause with `Windows completion is not validated`; this patch does not claim
that the original compiler otherwise completed successfully. A rebuilt runner
and fresh owned attempt are needed for end-to-end qualification.
