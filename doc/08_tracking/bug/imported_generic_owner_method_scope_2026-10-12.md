# Imported generic owner methods lose their binder scope

STATUS: OPEN. Candidate compiler source HIR-lowered; corrected compiler behavior and regression execution UNEXECUTED. Three-cycle cap reached; not merge-ready.

CaretSuite cs_main HIR lowers 165/169 modules; four SOSIX importers fail resolving Op/Cpl. Their actual SCV snapshot bytes match their source and contain neither name. SimpleRing<Op,Cpl> defines these names as owner parameters; importers provide SosixFileOperation/SosixCompletion.

A two-file Git-admitted reproducer contains GenericRing<Op,Cpl>, two pass-through method signatures, and a consumer Holder with GenericRing<i64,text>. The exact P2 producer emits four unresolved errors (Op twice, Cpl twice) and no object. No method call is necessary. The defect occurs during eager imported signature registration, before concrete specialization.

Source chain: register_imported_symbol creates a temporary declaration-binder scope for composite fields, projects them, then pops it. register_imported_type_methods subsequently projects method signatures without those binders. Callable.type_params contains only a method's own parameters, so it does not identify a method that is generic through its owner.

The candidate adds an owner-aware projection helper that saves/restores prescan parameters and scope. Method symbols are still defined after the temporary scope is popped. A binder-aware dependency walk excludes declaration binders while resolving all other names with the existing owner resolver. Existing exported method signatures remain unchanged, allowing the parent to replace only cached mod276.o and mod281.o after real compilation. The ordinary nongeneric dependency/projection paths remain in use. Five real HIR specs cover preserved TypeParam parameter/return shapes, name shadowing, scope non-leakage, rejection of missing types and concrete sibling dependencies.

The helper covers declaration-owner binders matching the confirmed SimpleRing case. Impl-specific renamed binders and generic trait-default metadata are preexisting separate boundaries and are not claimed fixed. ModuleSurfaceImpl currently drops impl generic parameter metadata.

Executable qualification requires actual changed compiler objects. A source overlay beside the frozen P2 binary does not change that binary's HIR implementation. No shadow-source PASS, Rust seed CLI fallback, fabricated cache marker or whole compiler rebuild was used. Root owns manual cached-object relink once the two actual provider objects exist. No post-fix performance/memory claim is made before that qualification. Minimal baseline command, source, receipt and logs are adjacent to receipt.json.

## Bounded executable qualification follow-up

The real per-module native object route exists: successful LSP/JSONRPC caches retain independently hashed ELF objects under objects/sha256. The first candidate build selected 257 modules and passed HIR 257/257 with both modified owner source hashes matching its SCV snapshot. It timed out at 240 seconds after enum-contract diagnostics, before native emission. No replacement object was produced.

A separate runtime-only P2 successor was then rebuilt from the original 1,218 compiler module objects. Its historical runtime translation unit was reproduced byte-for-byte before adding the verified seven-line empty-scope guard. All 244 dependencies and 1,221 original link-object hashes matched. Ownership, guarded-free, real native Hello and historical-runtime performance checks passed; its receipt is in ../simple-p2-runtime-empty-scope-relink-20261012 relative to the candidate root's parent. This successor changes no compiler logic and does not itself contain the binder fix.

The final attempt compiled a real HIR regression entry and its 299-module closure with that successor. It stopped with two diagnostics in the test entry: the imported parser name Module was stale; the declared type is ParserModule. This was copied from an existing repository spec and is a fixture mistake. The fixtures have been corrected in source, with no fourth build after the three-cycle cap. No native test execution or corrected-compiler behavioral PASS is claimed.

A bounded GDB sample of the actual worker showed rt_core_transient_raw_insert_raw -> register_enum_unit_patterns, table capacity 1,048,576 and live count 65,356. That is nonempty allocation work; it does not demonstrate failure of the empty-scope fix or a memory leak.

Cached P3 mod_276/mod_281 providers use Rust-style double-underscore symbols, whereas the successful P2 LLVM cache uses dotted names. Any future replacement requires actual emitted-object symbol/ABI compatibility, not symbol renaming or duplicate-definition suppression. A direct native HIR regression executable remains a valid independent route if compatible deployment objects cannot be produced. Upstream 88b20a3ba was checked read-only: both affected compiler owner files are byte-identical to the 523 base, so this candidate does not duplicate those upstream changes.
