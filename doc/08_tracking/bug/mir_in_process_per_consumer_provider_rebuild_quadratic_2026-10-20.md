# In-process MIR: per-consumer provider rebuild is quadratic in time and retained memory

Date: 2026-10-20
Status: OPEN. Diagnosis measured. Partial repair landed with this record (unmeasured, see below).
Related: `phase3_mir_retained_memory_2026_10_17.md`,
`mir_lower_child_tasks_append_access_violation_2026-10-19.md`.

## Symptom (phase 3, Windows, producer4 `simple-producer4-strict.exe`)

`SIMPLE_MIR_SHARDING=0`, `bootstrap_main.spl`, 1351 modules. Parse and HIR (sharded)
finish in about 3 min. In-process MIR then runs about 2 h on one core. RSS grows the
whole time, from 3.3 GB to more than 58 GB, and nothing is logged. The ICE breadcrumbs
(`build/ice/<run>/ice_breadcrumbs.<pid>.log`) were the only live progress signal: about
1246 `mir_lower` starts after 2 h.

## Repro (418 modules, same producer, 16 threads)

Entry: a scratch `src/app/mirrepro/main.spl` that imports
`compiler.mir.mir_lowering_types.{MirLowering}`. Run with
`native-build --entry-closure --backend llvm --runtime-bundle core-c-bootstrap`,
caches off, `SIMPLE_COMPILER_PHASE_PROFILE=1`, and
`SIMPLE_COMPILER_PHASE_PROFILE_FILE=<file>`. That file gets one durable line per
`log_phase` call, with `rss_kib` included. The worker stops after MIR on unrelated MIR
errors, so this run measures MIR only.

| measurement | value |
|---|---|
| RSS after HIR/typecheck | 2.9 GB |
| RSS at the first MIR module start (prescan, inventories, session index) | 4.3 GB |
| RSS after module 418 | 9.1 GB |
| growth inside `lower_module` calls / between them | 4.82 GB / 4 KiB |
| MIR wall time | 908 s for 8005 functions, about 2.2 s per module, linear in module count |
| modules with 5 or fewer functions (139 of them) | **1.64 s each on average, 420 MB in total** |
| heaviest single modules | `expr_dispatch` +607 MB / 8.6 s, `switch_operators_calls` +448 MB, `module_lowering` +332 MB |
| `method_calls_literals` (385 KB of source) | +0 MB but **67.5 s** |

`SIMPLE_MIR_SCOPE_TRACE_MODULE=<HirModule.name, which is the snapshot source path>`
on `expr_dispatch` printed `decisions=511 outcome=10`. The per-module transient scope
begins, promotes and ends successfully. Two traps hit while measuring: the selector
matches `HirModule.name`, which is the file path, not the logical module name. The
worker's stderr also reaches the coordinator log only on failure, and then only a
bounded tail. To see `eprint` traces, run the worker directly:
`<producer> run src/app/cli/native_build_worker.spl <args>
--internal-environment-variant-policy-v1=...`. Copy the handoff argument from a live
worker's command line, and reuse the coordinator's SCV snapshot.

## Diagnosis

1. **A fixed per-module cost scales with the size of the closure.** The 1-to-5-function
   modules take 1.64 s each and still add about 3 MB each. That cost is not their own
   lowering. It is `lower_module`'s prologue, which re-registers *every provider in the
   closure* for every consumer:
   - `register_provider_class` and `register_provider_struct`: every field type is
     relocated, every default is relocated, and the rows are rewritten into cumulative
     dicts such as `struct_field_has_default`, `struct_field_default_expr` and the
     composite metadata;
   - `register_trait_receiver_impls`: all impl rows go into `trait_impl_owners` and
     `trait_impl_methods`;
   - the native trait declarations and implementations;
   - the promotion walk itself. `rt_transient_heap_promote` walks persistent structs
     through the struct registry (`rt_transient_raw_words`), so each module walks the
     whole owner graph again.

   With N modules and P providers the total is N x P, which is quadratic. At phase-3
   scale (P about 1351) the same cost is about 3x larger per module. That roughly
   matches the observed hours on one core.
2. **Rebuilt per-consumer rows become immortal orphans.** Without a collector, a
   promoted value that the next module overwrites can never be freed. There are two
   ways this happens:
   - (a) Tables that the prologue resets for every consumer but that were not retired
     before promotion: trait-impl rows, imported-global mirrors, exact-extern
     signatures, collection-literal scratch. **Fixed here.**
   - (b) Cumulative dicts that are overwritten with freshly relocated, consumer-local
     values: the class and struct layout and default rows. **Still open.** Fixing it
     needs either demand-driven provider registration (register only the providers
     this consumer references, as `register_imported_global_bindings` already does
     for globals) or a per-consumer overlay that is reset and retired each module.
3. **Each module's MIR output stays live until codegen.** It is promoted into
   immortal storage. `SIMPLE_NATIVE_STAGED_CODEGEN_BATCH` evicts the references but
   cannot reclaim the memory (`native_staged_codegen.spl` header). Expect a large
   per-function share: about 0.5 MB per function at the 418-module scale.

## Why it is single-threaded

- One `MirLowering` instance carries cross-module mutable state: the provider
  session index, the declaration repository, the cumulative layout dicts, and the
  errors.
- The C runtime's transient scope has a **process-global owner** (a CAS on
  `rt_core_transient_scope_owner`) and is not reentrant. A second lowering thread
  could not reclaim anything. The immortal registry and the heap-lifecycle
  spinlocks would serialize it anyway.
- Lower, then codegen, then drop (the Go-style approach) needs the MirModule to stay
  owned by the scope through codegen. Every backend or driver write that persists
  past the scope would then have to be promoted, and that escape set has not been
  enumerated. Doing this without that proof risks use-after-free.
- The bounded and parallel path that exists today is process sharding
  (`SIMPLE_MIR_SHARDING=1`). It is blocked on the HIR cache codec refusing stores
  (another lane is working on it).

## Repair in this change (UNMEASURED: no runnable compiler from the patched source)

- `lower_module_transient_scoped` now retires the class 2(a) tables before
  promotion. This is the same pattern already used for `struct_method_*` and
  `native_trait_*`. Each table is reset unconditionally in the `lower_module`
  prologue before any read, and nothing outside 50.mir's synchronous lowering reads
  it. Ambient bootstrap keeps the tables (the flat emission reads the global
  mirrors).
- `[mir] i/N rss_mib=... elapsed_s=... module=...` every 50 modules and at the end.
  It goes to stdout, and to `SIMPLE_COMPILER_PHASE_PROFILE_FILE` when that is set.
  The file is the only live channel on Windows, where the coordinator captures the
  worker's stdout until the worker exits.

The before/after effect of the repair cannot be measured on this host. The repair
only takes effect in a compiler built from this source, and that build is phase 3
itself (more than 2 h and 60 GB). The producer4 object cache is gone, so relinking
is not possible either. Qualify on the next phase-3 run by comparing the `[mir]`
lines against the breadcrumb timeline above.

## Stage 3 bootstrap-fixed closure (2026-10-20, after #3938)

Passing the provider feed to the ambient-bootstrap closure lane re-enabled the
provider loop on a lane where both repairs above were switched off:
`ambient_bootstrap_enabled()` skipped the class 2(a) retirement and forced the
eager class 2(b) layout pass. The closure driver's `trait_impl_provider_modules`
(the whole closure HIR) was also an owner root, so every module's promotion
re-walked it. Repair: retire 2(a) for ambient non-entry modules, demand layouts
for them (`SIMPLE_MIR_EAGER_PROVIDER_LAYOUTS=1` restores eager), detach the feed
during promotion, and warn on a refused scope. Pinned by
`test/01_unit/compiler/50.mir/bootstrap_closure_provider_retention_spec.spl`.
Per-module RSS is unmeasured until a Stage 2 is rebuilt from this source: a 12G
probe with the r16b Stage 2 cannot reach MIR (it ended at `phase4:monomorphize`).
