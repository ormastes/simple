# Windows standalone core remove selected a legacy stub

Canonical bug database reconciliation is pending: no qualified self-hosted bug
database runner is available in this bootstrap lane.

The retained LSP cycle2 PDB/disassembly proves `rt_remove` at VA 0x1400194e0
returns constant -1. The generated `dir_entry_ops.spl` caller supplies tagged
text and expects deletion. runtime.c's Windows compatibility stub displaced
runtime_native.c's real tagged-text implementation in the runtime-first link.

Omit only that legacy stub on Windows standalone. The native implementation
also needs Windows wide APIs in this lane: its narrow stat/unlink path would
interpret UTF-8 through the ANSI code page. Use the existing UTF-16/long-path
helper, GetFileAttributesW and DeleteFileW/RemoveDirectoryW, preserving zero
success and negative errno results. Hosted Windows and Unix remain unchanged.

The focused native regression creates exclusive fixtures only beneath
`C:/dev/simple-bootstrap-storage/phase3-validation-20261016/core-remove-owner-regression/scratch`.
It checks creation/existence, actual deletion, missing-path ENOENT, UTF-8 and
space preservation, and empty-directory deletion. It never accepts an external
path or recursively deletes anything. Evidence belongs to the parent directory.

First focused compile/link/run passed: exit 0, empty stderr, explicit checks
confirmed real file deletion, ENOENT on the missing file, and empty-directory
deletion using UTF-8/space paths. The owned scratch directory was empty after
the run. The native/core archive link used no FORCE, ignored undefined symbols
or fake providers. Standalone runtime.obj has no rt_remove definition and the
native object defines it strongly; compiling hosted runtime.c without standalone
retains its previous definition. Full mixed-tool qualification is separate.
