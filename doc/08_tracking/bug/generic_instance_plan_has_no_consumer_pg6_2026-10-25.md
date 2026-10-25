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
