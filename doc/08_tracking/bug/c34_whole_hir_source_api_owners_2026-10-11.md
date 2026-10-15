# C34 whole-HIR source API failures

Frozen source `20a93224b3f08a86a15b520252bd95965f1e6423`, producer
`f00dbc9c608dfaf22a15736747799821ed1b75871bf45ad3fe1b133701030e81`.
Retained evidence is under
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c34-cold-hir-attempt1/canonical-whole-phase3-attempt1/`:
`hir-ledger-summary.json`, `build.log`, and `cache/hir`.
The ledger records 439 PASS, four FAILED, one claimed without a terminal, and
781 unattempted of 1225. The run stopped at its RSS cap before MIR/object work.

Six fatal diagnostics comprise three concrete source/API defects and one
unresolved type-projection failure:

| Consumer | Actual diagnostic and physical owner | Correction |
|---|---|---|
| `40.mono/monomorphize/deferred_deserialize.spl:482` | Unresolved `deferred_last_error`; variable declared at `deferred_subst.spl:20`, but consumer imported only `deferred_set_error` | Import the existing variable from the same owner; retain one mutable error state |
| `40.mono/monomorphize/tracker.spl:69` | Unresolved free function `notesdnmetadata_new`; actual API is `NoteSdnMetadata.new` at `note_sdn.spl:227` | Call the declared static constructor, preserving its reverse-reference registration side effect |
| `compositions/kernel_llvm_cranelift/compiler/driver/bootstrap_k1_selected.spl:54,60` | Unresolved `error` at both rejected K1-install branches | Return existing `CompileResult.CodegenError(text)` immediately |
| `80.driver/driver.spl` | Two unresolved `ImplBlock` diagnostics, without spans | Unresolved; no speculative change |

The metadata and deferred-state physical providers each have C34 PASS ledger
records. `std.error.error` merely constructs a `SimpleError`; importing it in
the composition would discard that object and continue combined compilation.
The declared return type is `CompileResult`, whose `CodegenError` variant is
unsuccessful and retains the message through `get_errors`. Rejected admission
must terminate before the combined compilation calls.

Compared with C33, `compile_options`, `compile_targets`, and
`full_static_backend_registry` now have actual PASS records. The composition's
old CodegenOutput errors are absent; its two remaining diagnostics are above.
`arch_rules` has no terminal record in this whole-HIR ledger, so no PASS is
claimed. Driver re-export traces still reach `compiler.traits.trait_impl`,
whose physical module declares `ImplBlock`; they do not identify the imported
signature causing the two errors. Correcting these three APIs does not claim
to resolve driver type projection.

The affected consumer/provider files are unchanged between C34 and release
`28a3b183b427bb524c13726424ecbf0b89acf6be`, the isolated patch base.
Focused SSpec and a standalone real-composition rejection fixture are authored
in this change. Native execution, regression execution, full verification,
and whole Phase 3 qualification remain pending. No seed fallback was used.
