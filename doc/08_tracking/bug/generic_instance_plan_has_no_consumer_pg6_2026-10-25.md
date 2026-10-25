# P-G6: generic instance build plan has no consumer, and function templates have no ConcreteTldrKey

**Status:** open. This is P-G6 scope.
**Filed by:** P-G5 (#4628)

## Gap 1: nothing consumes the instance build plan

`src/compiler/80.driver/cache/generic_instance_build_plan_v1.spl` does three things:

- unions every module's TLDR `generic-spec` list into the set of needed instances (`ConcreteTldrKey`);
- partitions the instance-object cache by producer identity (`file_worker_inc_producer_v1`) and verifies each cached object by its recorded header;
- computes which instances to build, reuse and drop.

Nothing calls it yet. As a result:

- Instances are still emitted once per using object, with COMDAT linkage. No per-key instance object is built once and then linked.
- The scheduler never reads `GenericInstanceBuildPlanV1`.
- `drop` deletes nothing.

What closing it needs:

1. The file-worker scheduler calls `generic_instance_build_plan_of_tldr_v1` before the MIR rounds.
2. The scheduler builds each key in `build` once. The body comes from the P-G4/P-G5b template-body loader. The scheduler publishes the result with `generic_instance_cache_publish_v1`.
3. The linker links the instance objects.
4. COMDAT copies are retired from using objects only when the plan is `complete`.
5. Objects under `drop` are deleted.

## Gap 2: generic function templates are not keyed

TLDR `generic-template` entries only cover generic structs and classes. `module_generic_template_decls_of_module_v1` handles only those. A module that instantiates an imported generic **function** cannot get a `ConcreteTldrKey` row for that instance. Two examples: `id(1)` places `id$i64`, and `make_pair(1, 2.0)` places `make_pair$i64_f64`.

Because of this, P-G5 marks that module's list incomplete (`generic_specializations_of_mono_v1`, `fn_instances`). The planner then falls back to the interface-digest rule. In practice, exact generic invalidation stays off for every module that calls an imported generic function.

What closing it needs: project generic function templates into the TLDR `generic-template` section and key their instances through `concrete_tldr_key_for_v1`.

## Repro

- `test/01_unit/compiler/cache/generic_specialization_mono_v1_spec.spl`: case "an imported generic function instance with no type use keeps the list incomplete".
- `test/01_unit/compiler/mono/mono_module_scoped_spec.spl`: case "records an imported generic function instance with primitive arguments (P-G5)".

## P-G6 progress (2026-10-25)

Closed by `src/compiler/80.driver/driver_build/native_file_worker_instances_v1.spl`
and its call in `run_file_worker_pool_v1` (`src/app/cli/native_build_main.spl`):

- Step 1: the coordinator plans from every module's fresh TLDR list after the
  module objects exist (no barrier before the first object).
- Step 2 (scheduling half): each key in `build` is a single-flight job
  (exclusive mkdir claim in `<mir ledger>.instances`) with a PASS/FAILED
  receipt; a built object is published with `generic_instance_cache_publish_v1`;
  the previous needed set is persisted per producer.
- Step 5: keys under `drop` have their object deleted, and a build or drop
  forces a relink (P-E removed-module rule).
- Fail closed: an incomplete plan runs no job. COMDAT retirement and instance
  linking need a complete plan, every key verified, and COMDAT-linkage
  instance objects, so no instance gets two strong definitions.

Still open:

- Step 2 (object half): no instance-object producer exists (template body ->
  object codegen). The pool passes a producer that returns no object, so
  every claimed key fails closed with a FAILED receipt.
- Steps 3-4: the linker does not consume `link_objects`, and using objects
  still emit their COMDAT copies. Both are blocked on the producer above.
- Gap 2 is closed: `module_generic_template_decls_of_module_v1` projects generic functions into `generic-template` (no fields; `source_digest` covers signature and body), and mono's imported function instances are passed as uses, so `id(1)` keys as `t.id` + [i64] through `concrete_tldr_key_for_v1`. An instance whose template is not visible still makes the list incomplete.

## P-G7 progress (2026-10-25)

`src/compiler/80.driver/driver_build/generic_instance_object_producer_v1.spl`
adds the producer and the link wiring:

- Producer (step 2, object half): module-scoped mono records the mangled
  symbol of every imported generic-function instance; the MIR child keys it
  (`module_tldr_instance_keys_from_mono_v1`, same templates/context as the
  `generic-spec` list) and, after the using module's object compiles, codegens
  that one COMDAT function alone through the same backend/target/CPU/storage
  snapshot (`_stage_generic_instance_objects_v1`, `driver_aot_native_output.spl`)
  and stages it under the key (first writer wins). The coordinator's
  single-flight job reads the staged object (`generic_instance_object_from_stage_v1`)
  and publishes it to the producer-keyed, header-verified cache.
- Step 3: the coordinator extracts each verified object body and passes the
  list via `SIMPLE_FILE_WORKER_INSTANCE_LINK`; `aot_link_mir_shards_v1` links
  them once, after the module objects.
- Step 4: the needed set is recorded retirable only after a run where every
  key PASSED. The next build snapshots retirable keys whose object verifies
  (`SIMPLE_FILE_WORKER_INSTANCE_RETIRE`); MIR children drop exactly those
  COMDAT copies and the link links exactly those objects. A retired copy with
  no verified object blocks the link (fail closed).

Still open (keys fail closed, nothing retired for them):

- Instances that touch a module global (LoadGlobal/StoreGlobal/GlobalAddr)
  are not extracted.
- Generic TYPE instances (methods keyed by a `Name<args>` use) have no
  symbol -> key mapping yet.

### P-G7 review r1 fixes

- Body identity: the cache key is ConcreteTldrKey + sha256 of the template
  owner's current source (`generic_instance_lists_with_body_v1`), so a
  body-only edit changes the key: the old object is dropped, the instance is
  rebuilt, and the retire snapshot drops rows whose owner digest changed.
- Bytes: instance objects are byte-copied (`file_copy`) at stage, cache and
  link; the cache header is a sidecar `<object>.hdr` over the object's
  `file_hash_sha256_or_empty` digest; link copies are re-verified.
- Extraction also rejects instances that name a constant, static or
  non-instance function of the using module.
