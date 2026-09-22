# Cranelift module symbol projection

Status: native naming projection red/green and nineteen contracts PASS with
the separately qualified real runtime provider. Full adapter/Stage2 admission
is not claimed. See QUALIFICATION.md for exact provider composition.

`probe.spl` calls actual Cranelift wrappers to emit two objects with same-leaf
functions owned by alpha/beta, then a caller importing alpha.value/beta.value.
The intended final native result is0 (42+99-141). `contracts.spl` separately
covers naming priorities and canonical entry-path decisions; all19 passed.

Generate symbol_support.spl from support_prefix.spl, the production
mir_runtime_owned_call_name/mir_runtime_owned_local_symbol functions in
src/compiler/50.mir/mir_call_ownership.spl, and the range from
`fn cl_is_lowering_owned_runtime(` to the following Helper Functions section
in src/compiler/70.backend/backend/cranelift_codegen_adapter.spl. Green also
imports compiler.common.module_path_naming.module_logical_name_from_path.
Red uses the baseline range, green the working range, both verbatim.

The small harness wrapper `probe_emit_name(name, owner)` calls the baseline's
one-argument helper on red. Green constructs a modeled MirFunction with name,
export_name, is_global, then calls the actual four-argument helper with
is_entry=false/no_mangle=false. No MIR instruction/type lowering is projected.
Green `probe_emit_name_full` exposes all naming inputs to contracts.spl, and
`probe_entry` delegates to the actual entry-policy function. Modeled function
records contain only the fields consumed by those exact production helpers.

Preserved assembled sources and artifacts:
`/Users/ormastes/simple-tmp/stage2-result-identity-20260923/build/native_probe/module-symbols/{red,green}`.
The producer is frozen runtime-authority/simple from the b910 Stage2 evidence.
Each build used strict no-stub fallback, private per-variant caches, LLVM23,
Cranelift two threads, and the5859375 KiB watchdog (build180s/run20s).
Cycle1 core-C links then traps at rt_cranelift_new_aot_module_triple.
Cycle2 dynamic-runtime rejects this non-Stage4 entry. Cycle3 core-C with
SIMPLE_LINK_OBJECTS naming the frozen compiler backfill still links a trap.
No further attempt is permitted in this lane. The exact working assembly is
preserved for a separately qualified runtime-provider task.

The above artifacts and failed cycles are preserved unchanged. After a
separate provider qualification and reviewed macOS guard-page repair, the
same projections were verified in the new cranelift-provider-naming-20260923
worktree. Native contracts now cover library-main, export/global, local alias,
no-mangle, and canonical entry policy. Red objects expose the symbol mismatch;
green objects link and execute0. Full adapter/MIR execution and local-alias
lookup are statically reviewed only; export/global cases test naming rather
than the complete ABI. SSpec remains unexecuted. The separate capsule identity
rejection remains open, as does the pre-existing library-main ABI limitation.
