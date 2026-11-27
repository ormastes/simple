# Native cache: whole cwd source tree in the producer identity

Date: 2026-11-24. Status: object cache narrowed for linked shard/unit workers only (not verified by a build or a spec run); everything else still tree-bound.

## Symptom

In the pure-Simple `native-build`, editing one line of one file under `src/lib` or `src/compiler` renamed the object scope directory and changed every module witness, so all modules of a compiler self-build recompiled.

## Why the fingerprint was there

`native_build_compiler_identity` folded `compiler=<src/compiler fp>+stdlib:<src/lib fp>` (`src/compiler/80.driver/driver_build/incremental.spl`). Both terms were added for an INTERPRETED compiler: the seed runs the compiler from those `.spl` files, so an edit changes codegen while the executable hash stays equal (docstring of `native_build_compiler_source_fingerprint`; commit `d73fddde667` for `src/lib`). Nothing distinguished that from a compiler linked into the executable, for which the same trees are only the sources being compiled.

## What changed

`native_build_object_producer_identity(debug_info)` is used for the scope directory and the witness config (`driver_aot_native_output.spl`). It keeps the tree term by default and drops it only when ALL of these hold (`native_build_source_tree_is_producer_v1`):

1. The process took the CLI branch that dispatches a marked coordinator child to the worker entry linked into the image (`src/app/cli/bootstrap_main.spl`, `src/app/cli/_CliMain/main_and_help.spl`); that branch calls `native_build_declare_linked_worker_entry_v1()`. Nothing is inferred from the runtime-kind probes alone: they are constant `false` in the C and pure-Simple runtimes, so a `run <x>.smf` host or a cached-SMF interpret looks native to them. The probes remain as a second gate.
2. The hashed executable is the running image.
3. No debug info is emitted (spans feed debug info and are not in the MIR identity).
4. The worktree root is known.

When dropped, the term is `embedded+worktree:<sha256(cwd)>`: objects are stored per module name and the default link does not re-hash them, so two worktrees must not share a scope directory.

In-process builds (including managed bootstrap stages, `SIMPLE_BOOTSTRAP=1`), the coordinator's in-process fallback and every debug-info build keep the old identity. Every other consumer keeps `native_build_compiler_identity()` unchanged.

The capsule MIR identity now also carries the emitter-read attributes it used to omit (`native_capsule_mir_identity.spl`): function `is_naked`, `is_inline`, `section`, `align`, `is_global`, `is_comdat`, the SIMD requirement, `nogc_strict`, `short_call_contracts`; static alignment, linkage and `is_external`; module `xray_ring_wrap`. Each is appended only when not at its default, so ordinary identities are unchanged and only modules using them miss once.

## Inputs from the source tree that can reach an object

| Input | Reaches the object through | Bound per module |
|---|---|---|
| Module's own source | its MIR | yes: MIR identity; disk identity check `driver_aot_native_output.spl:2904` |
| Imported signatures, fields, enums | lowering | yes: dependency slice fold, `cache/native_module_witness.spl:167` |
| Generic instantiation, inlined/default bodies, const and static initialisers, AOP advice | consumer MIR (lowering always runs on this path) | yes: MIR identity hashes every function body, const, static and type |
| Emitter-read function/static attributes of such bodies | consumer MIR | yes, since this change (see above) |
| Spans of such bodies | debug info | not in the identity; debug-info builds keep the tree term |
| Implicit/prelude imports, global trait impl lookup, cross-module lowering inventories | consumer MIR | yes, structurally, by the same MIR identity |
| Layout of types owned by modules not imported | emitter | yes: layout fold |
| Import resolution | lowering | yes: resolution fold, `cache/native_module_witness.spl:168` |
| Typed storage registry (whole-build) | capsule snapshot | yes: `storage=` in options identity |
| cfg guards, environment, target, backend, opt | emitter | yes: scope key and config fingerprint |
| Emitter module-level globals | emitter | none found: string-global builder resets per module (`_MirToLlvm/core_codegen.spl:486`); `spec_const_registry` is CUDA/OpenCL only; `enum_semantic_declarations` is not read under `70.backend` |
| Shared `backend_session` lease passed to the emitter | emitter | NOT examined |

The emitter receives `capsule.mir_module`, `capsule.storage_snapshot`, `target_cpu`, `backend_session`, output base and name; the batch and `CompileContext` are not passed.

## Still tree-bound, and why

- **MIR resume ledger.** The run key carries the tree-bound compiler identity (`driver_build/native_mir_shard.spl:481`, built in `src/app/cli/native_build_main.spl`). Adoption checks receipts only and the link compares the inventory to an interface-only source fingerprint, so the tree term must stay there.
- **Pre-lowering cache** (opt-in) and **no-op admission** skip lowering, so no MIR identity protects them.

Consequence: after an edit the ledger is rejected and every module is lowered again; only codegen is saved, and only in linked workers, for modules whose MIR identity is unchanged. In the serial lane a symbol added early can shift later symbol ids, and the whole-build `storage=` identity (its site rows include a source revision) can change, either of which misses safely. The benefit is unmeasured.

## Not confirmed

- **Ledger resume hazard.** An earlier draft of this record claimed a body-only edit outside the two trees (`src/app/**`) could be adopted and linked stale. That was NOT confirmed: the run key's environment term folds the `SIMPLE_SCV_*` snapshot rows, which are per-file content digests published before the shard pass, so such an edit changes the run key. The inherited-snapshot case and the managed-bootstrap path were not checked.
- **Hand-made invocation.** A host that executes a compiler SMF whose `main` is then given the worker argv and marker by hand would set the marker without being linked code. The coordinator never spawns that shape: its children are `<exe> run src/app/cli/native_build_worker.spl`, which a self-hosted image intercepts before any `run` handling, and the seed is refused as a worker runtime.
- **Phase 2 to 3 materialisation** compares the witness config identity; not analysed.
- `serialize_mir_function` losslessness for instruction-level detail is assumed.

## Other notes

- `sh scripts/check/check-no-direct-rt.shs --roots src` fails identically on `release/1.0.0` and on this branch (`7012` vs baseline `6290`): pre-existing; this change adds no call outside the allowlisted `process_ops.spl`.
- No build and no spec run was possible (a multi-hour compiler build held the host; no full test binary).
