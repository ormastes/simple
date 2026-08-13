# Stage3 numeric interpolation corrupts AST hardening slot (2026-08-13)

Status: Pure-Simple MIR/LLVM root-cause fix implemented; native rebuild and
runtime confirmation remain required because the frozen Build10 executables
crash before focused compile/test execution.

Build9 GDB evidence is retained at `/mnt/data/bs2/packed-memory-build9/gdb-replay/gdb.txt`.
The failing `ast_gen_harden_enabled` load uses `rcx=0x393333373038`, whose little-endian bytes are ASCII `807339`, exactly the preceding `heap_registry=807339` diagnostic value. The array backing pointer for `ast_gen_harden_slot` was therefore overwritten by a numeric-to-text representation. The fault occurs before scalar unboxing; this is not a tuple ABI or AST-hardening predicate defect.

The temporary containment removes dynamic `rt_heap_registry_count()` interpolation from active phase2 and memory-snapshot diagnostics while preserving path, sequence, phase, timing, and live/peak fields. It covers the canonical Build9 environment (`SIMPLE_COMPILER_PHASE_PROFILE`, `SIMPLE_COMPILER_TRACE`, and `SIMPLE_MEM_SNAPSHOT`); those diagnostic owners now contain no heap-count interpolation. Generic numeric interpolation remains enabled elsewhere and is not fixed by the containment change.

The Pure-Simple root fix keeps `rt_raw_i64_to_string` and the other scalar
renderers nominally `i64`: they return tagged runtime-string handles.
`rt_interp_cstr(i64) -> ptr` is the one explicit raw-C-string conversion before
`rt_strcat`; a renderer result is never nominally `Opaque("str")`. LLVM lowering
now registers the same `i64` renderer returns and `ptr` bridge return, so the
generated call sequence preserves the tagged handle before the pointer
conversion. Focused coverage includes numeric extremes, generic interpreter
interpolation, emitted MIR-to-LLVM call shapes, and two
`parser_init_with_path`/`ast_reset` cycles after the diagnostic shape.

Native runtime confirmation is pending a working self-hosted Build10 binary:
the frozen release wrapper fails its bounded `test --help` probe, while the
frozen Stage3 executable segfaults (exit 139) on both the focused SMF compile
and direct native build of the monomorphic numeric diagnostic probe.
