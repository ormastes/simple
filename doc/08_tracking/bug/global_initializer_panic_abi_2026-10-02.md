# Module initializer cycle diagnostic ABI

The imported-global initialization guard emitted a direct MIR `rt_panic`
call with one raw string pointer. `runtime_native.c` implements this entry as
`rt_panic(const uint8_t*, uint64_t)`, and the LLVM backend declares `(ptr, i64)`.
Direct builder calls bypass expression-level text argument expansion, leaving
the diagnostic length undefined on the failure path.

The guard now emits the message length explicitly and records the matching
two-parameter function signature. The regression spec examines the generated
guard call and length constant. The existing three-module
`test/fixtures/compiler/imported_globals_cycle` graph remains the native oracle:
nonzero exit with an anchored cyclic module-global initialization diagnostic;
timeout, signal, or successful execution is not a pass.

Validation: source ABI inspection completed. Unit/native execution is UNRUN.
The exact d6 qualification producer failed linking generated HIR helpers before
an executable existed; that independent failure must be repaired before native
qualification. No immutable producer source was modified for this follow-up.
