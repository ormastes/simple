# Generic-instance TLDR + pre-link instance generation (v1)

Status: plan, 2026-10-27. Owner: generic-instance lane. The per-file lane
(PM1-PM3: HIR gate, default route, in-process invoker) is NOT changed here.

## What already exists (do not rebuild)
- Per-module used-instance list: TLDR section `generic-spec/v1` with a
  `complete` flag, written by `module_tldr_update_generic_spec_from_mono_v1`
  (`80.driver/cache/module_artifacts_v1.spl`) after module-scoped mono.
- Instance key: `ConcreteTldrKey` (`concrete_tldr_key_v1`,
  `00.common/cache_contract/generic_tldr_view_v1.spl`) = owner TLDR id +
  generic name + canonical concrete type args, stable hash.
- Body identity: `generic_instance_body_key_v1(concrete_key, body_digest)`,
  body digest = owner source digest + direct-import interface digests.
- Planner + jobs: `generic_instance_build_plan_v1`,
  `run_file_worker_instances_v1` (single-flight claim, receipts, producer-keyed
  header-verified cache, removed key forces relink).
- Backends already emit COMDAT/linkonce_odr for `is_comdat` instances (LLVM,
  Cranelift; ELF group / COFF `SELECT_ANY`).

## The gap
The pre-link step runs ONLY on the opt-in file-worker pool
(`SIMPLE_FILE_WORKERS=1`). The default shard path (parse/HIR/MIR shards ->
`run_mir_shards`) passes `file_worker_active=false` to
`mono_module_scoped_selected_v1`, so it runs whole-program mono after all MIR:
that is the 6 fixed stages and the late first object seen in phase-3 run 6.

## Instance key format
`gi1:<owner_tldr_id>:<generic>:<canon_type_args>#<xxh3>`; cache key =
`instance_key + template_body_digest + producer_identity` (producer =
`file_worker_inc_producer_v1`, includes lane scope).

## Owner rule
1. Using objects emit instances as COMDAT (`SELECT_ANY` / linkonce_odr) -- never
   strong -- so duplicates are legal on ELF and COFF (windows-gnu, lld).
2. When the plan is complete, the canonical instance object (one per key,
   claimed once) is linked and the COMDAT copies may be retired.
3. Incomplete plan -> fail closed: no instance object, COMDAT copies stay.

## Pre-link step (both lanes)
`needed = U generic-spec(all modules)`, `present = verified cache objects`;
build `needed - present` in parallel (claimed, cached), add to link set, link.

## Shard interaction (PR plan)
- PR1: this doc + two-module e2e spec (A defines `Box<T>`, B uses `Box<i64>`,
  `Box<text>`) on the file-worker lane: per-file compile -> pre-link instance
  generation -> link -> run.
- PR2: shard path selects module-scoped mono per claimed shard and calls the
  shared pre-link instance step at `outcome == "link"`; whole-program mono only
  with `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`.
- PR3: per-template body digest in TLDR (DEFINES rows) so one template edit does
  not invalidate every instance of its module.
