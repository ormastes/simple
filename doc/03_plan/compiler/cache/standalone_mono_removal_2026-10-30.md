# Standalone monomorphization removal

> **SUPERSEDED (2026-11-01):** monomorphization was deleted by commit `200a05f5bc8` (`src/compiler/40.mono/` no longer exists on `origin/release/1.0.0`); the statement below that the engine "is NOT removed" is obsolete. Current plan: `doc/03_plan/compiler/generics/generics_refactoring_formal_verification_plan_2026-10-31.md` (§1A).

Status: design and two dependency-removal slices; runtime qualification blocked.
Source baseline: `6a44812d73d6`. User requests removal, retaining valid generics.
Astra owns design and final source review; Luna owns implementation/specs.

## Actual callers and constraints

`80.driver/driver_hir_pipeline_passes.spl` invokes both whole-program report
and per-module specialization. `80.driver/cache/hir_mono_archive_consumer_v1.spl`
uses the pass for admission. The landed replay slice removed its pass
construction: `hir_mono_replay_selection_v1.spl` now filters already-published
templates through the HIR owner. `70.backend/linker/lazy_instantiator.spl`
uses `TemplateInstantiator`. Removing the driver call alone is incomplete.
`50.mir/_MirLowering/function_lowering.spl` rejects unsubstituted TypeParam
and Any; neither type erasure nor silent template omission preserves semantics.

Existing evidence inventory: `test/01_unit/compiler/mono/` contains rewrite,
specialization breadth, symbol identity, exception traversal, static factories,
and generic flow specs. `test/fixtures/compiler/hir_mono_archive/` contains
nested/recursive demands and owner collisions; adjacent nominal, current,
logical and verification-use fixture directories cover archive identity.
Some older manuals describe superseded lowering behavior; presence is not PASS.

## Replacement architecture and bounded migration

Keep generic declarations in target-independent HIR. At the existing configured
HIR-to-MIR owner, demand concrete function/type layouts using declaration owner
identity, concrete arguments, target/configuration and producer/ABI identity.
Resolve bodies through the existing HIR archive owner; memoize demanded bodies
and deterministic recursive worklist closure under that owner, retaining cycle
limits and diagnostics. MIR receives concrete types and explicit configuration.
Keep nominal relocation, address-taken functions, trait dispatch and exported
specialization symbols stable. Reuse current substitution logic initially;
moving or renaming its pass does not constitute removal.

Existing migration owners are `generic_instance_build_plan_v1.spl` and
`driver_build/native_file_worker_instances_v1.spl` for required-instance jobs,
`driver_build/generic_instance_object_producer_v1.spl` for object production,
and `hir_mono_final_repository_v1.spl` for admitted current-body publication.
The first already treats missing/incomplete demand lists as incomplete and
falls back to scoped specialization: that fallback must be replaced before
deletion. `generic_instance_cache_v1.spl` is an in-memory cache contract, not
proof of MIR/object producer integration. Retain target-neutral ConcreteTldrKey
semantic identity; attach target/layout/ABI/backend/configuration to the
existing artifact/producer key, not to source declaration identity. Preserve
the existing object-to-HIR-to-AST provenance chain and do not invent a second
instance scheduler or key family.

The coordinated RR lane owns canonical `GenericDemand`: committed unique
uses determine concrete template/argument instances, target/variant artifact
identity, and Interface/Const/Inline/AddressableCode/Export needs. Type-only
uses must not demand objects. Reuse admitted artifacts, close transitive demand
before link sealing, and remove zero-use demand without deleting pinned
artifacts. This lane does not edit the RR producer, demand interface, existing
build planner or object producer in its first slice; their owner is the
reverse-references lane. Standalone-pass removal must consume that boundary,
not rediscover demand through an independent whole-program scan.

1. Remove replay's unnecessary pass construction: replay consumes published
   functions and metadata; it must never create a new specialization scheduler.
2. Separate substitution, demand collection and deterministic publication from
   global module orchestration. Route configured HIR-to-MIR requests to existing
   archive/cache owners; preserve all generic forms and missing-body failures.
3. Migrate global/module driver and linker lazy consumers to those requests.
   Version persisted producer contracts where their meaning changes. Do not
   reinterpret existing archive bytes under a new identity.
4. Remove unreachable pass entrypoints and stage only after real output,
   archive replay, configuration isolation and linker equivalence gates pass.

## Luna first-slice contract

Scope: new `compiler.hir.hir_function_selection_v1` helper owner, existing
integration helper definitions/re-exports, archive replay consumer, and focused
real-HIR specs. No changes to async containers, target selection or other lanes.

Move `sorted_function_indices` and `is_generic_function` unchanged to the HIR
helper owner; retain explicit compatibility re-exports from the old integration
module. Add `hir_prune_published_templates_v1(module, emitted_templates,
unresolved_templates)` with `[text]` name lists. Retain ordinary functions,
zero-emission generic templates and every unresolved template. Remove only
genuinely generic definitions whose exact name occurs in emitted metadata.
Use existing nil handling; preserve module metadata and specialization bodies.
Archive replay calls it directly after all current identity/admission checks;
remove replay's pass and body-mode imports/construction. Existing production
pass pruning stays unchanged in this bounded slice.

Tests must construct real HirModule/HirFunction values and invoke the helper,
not a miniature reimplementation. Assert emitted removal, unresolved precedence,
ordinary-function retention, zero-emission retention, flag-only generic handling,
specialization retention and ascending stable function ordering. No vacuous
assertions, no placeholder helpers. No compiler/test/native-build execution:
the diagnostic cycle budget is exhausted and no qualified CLI is available.

## Completion and qualification

Second independent removal slice: delete the unused legacy `Monomorphizer`
field/allocation from `MonomorphizationPass`. Production references consist
only of field declaration and constructor initialization. Existing demand
qualification specs inspect its empty tables; replace those obsolete checks
with real canonical specialization-to-template/module ownership checks while
retaining concrete body, deduplication and template immutability checks.
The substitution function imported from the engine remains necessary.

Remaining active orchestration inventory:

| Owner | Remaining dependency and next required work |
| --- | --- |
| `driver_orchestration.spl` | Explicit compilation and ordinary pipeline invoke `monomorphize_for_explicit_compilation` / `monomorphize_impl`; replace only after configured demand provider can close all reachable calls. |
| `driver_source_llvm_ir.spl` | LLVM source output uses explicit specialization; must share the same demand provider. |
| `driver_hir_pipeline_passes.spl` | Global `run_monomorphization_with_report` and scoped `run_monomorphization_module_scoped_v1`; remove scheduling after provider parity, retaining publication diagnostics. |
| `hir_mono_archive_consumer_v1.spl` | Admission still accepts a collector; replace with immutable declaration/nominal facts from HIR owners. |
| `mono_archive_registration_v1.spl` | Scratch collector constructs the pass; migrate collection into owner admission without executing a module pass. |
| `mono_archive_state_v1.spl` | Scratch pass rewrites each demanded body and yields deltas; extract configured function substitution/rewrite context with existing relocation and budget invariants. |
| `driver_hir_archive_mono_execute_v1.spl` | Existing root-first/FIFO closure drives archive work; consume committed RR demands while preserving recursive closure and exactly-once publication. |
| `70.backend/linker/lazy_instantiator.spl` | `TemplateInstantiator` is still used for missing symbols; route demands through the same configured provider and preserve template package/native symbol behavior. |

The hard cutover gate is a qualified concrete-MIR provider preserving generic
functions, structs/classes/layout, methods, trait dispatch, address-taking,
exports, recursive demands, nominal owner collisions and unavailable-body
diagnostics. Existing interface/cache declarations and source inspection do
not satisfy it. No qualified compiler execution is allowed under the exhausted
diagnostic budget, so deleting these callers now would silently break valid
generics or replace explicit failures with missing definitions. This is a
qualification blocker to cutover, not permission to claim full removal.

First-slice source review must establish replay no longer imports or constructs
MonomorphizationPass, helpers preserve prior ordering/classification, and filters
preserve unresolved/ordinary definitions. This is dependency removal only.
Final Astra source review: the replay helper preserves exact-name emitted
selection, unresolved precedence, ordinary definitions, untouched module
metadata and the zero-emission return. Ordering/classification helpers retain
their original algorithms and compatibility exports. Review caught and Luna
fixed missing engine imports (`specialize_function_with_types`, `mangle_type`)
and an incorrect retained-function test count (four, not five). Real-HIR tests
now exercise those selection cases; existing demand tests check canonical
template/module ownership instead of deleted unused engine tables. Luna's
post-fix `git diff --check` passed. No syntax/runtime/ABI qualification is claimed.

Full standalone monomorphization removal remains unfinished until steps 2–4
and qualified generic/native/archive/linker regressions pass. Core compiler,
library, MCP/LSP checks, runtime and native MCP smoke remain UNRUN. No push,
merge, release or completion claim is authorized by static review alone.

## 2026-10-31 audit after PR 5518

Audit baseline: `0423140a092`. PR 5518 (`e0a16c5c669`) strengthens prelink
demand identity; it does not implement a replacement specialization producer.
`file_worker_instances_plan_v1` / `generic_instance_demands_v1` aggregate
per-module forward lists and validate cached objects. The latter explicitly
does not retain invocation-site counts or Interface/Const/Inline/AddressableCode/
Export needs. `generic_instance_object_producer_v1.spl` still consumes MIR
created by the child AFTER module-scoped monomorphization; its build callback
publishes already-staged objects. This is cache/reuse wiring, not independent
cold instance generation: `native_build_main.spl` passes
`generic_instance_object_from_stage_v1(stage, _1)` as the actual prelink build
callback. Generic-type methods have no symbol-to-key mapping;
non-extractable instances that reference module-local symbols are deliberately
retained in their original objects. These exclusions must remain fail-closed.

### Rejected zero-generics shortcut

The global pass's zero-definition shortcut cannot simply be copied into
`process_module_scoped_v1`. In scoped mode, `rewrite_call` invokes
`module_scoped_visibility_check_v1` even when no generic definition was
collected. An imported generic function whose provider is absent still needs
E-MONO-040, which makes the driver widen its template set or fail without an
object. Zero collected generic functions/structs/classes is not proof of zero
generic demand. `MonoPreflightFactsV1` contains resource counts, not this proof.

The existing real-HIR `mono_module_scoped_spec.spl` missing-provider case now
also asserts all three generic counters are zero and unresolved calls is one.
It retains its exact diagnostic and zero-instance checks. This is authored
UNRUN evidence; no new production skip was added. An equivalent-cost whole
body scan would merely replace the rewrite walk without establishing useful
removal. An empty-module-only shortcut is not the requested migration.

### Next concrete slice: independent cold instance producer

The next implementation must make one existing per-instance job able to build
a concrete function from admitted archived HIR without waiting for any using
module's `process_module_scoped_v1` or pre-staged MIR. Initially constrain this
to exact function templates already supported by the extractable-instance
policy. Unsupported nominal-method/local-symbol cases stay on the existing
route and must not receive a success/retirement receipt.

Proposed boundary (design only, no callable API or stub is added here):

1. The existing instance job supplies its `RequiredSpecializationV1`, exact
   template body key, producer/artifact key and owned registration authority.
   Admit canonical type arguments in declaration coordinates through existing
   template signature/nominal relocation owners. A textual TLDR key alone is
   not authority to invent types, substitute Any or load unrelated bodies.
2. Add an owner-private external-demand admission operation beside existing
   archive queue admission. It validates template identity, arity, concrete
   argument identity and body availability, then creates the same deduplicated
   specialization request that current root rewriting creates. Callers never
   append queue rows or manufacture symbol ids directly.
3. Reuse archive one-instance substitution, body rewrite and FIFO closure
   (`mono_archive_drain_one_v1` and publication/apply owners), keeping nested
   demand limits, diagnostics, exact-once state transitions and relocation.
   This is a function-production transaction, not a completed module pipeline.
   Do NOT forge `mono_archive_roots_complete_v1`, clear its root inventory or
   bypass `mono_archive_execute_next_specialization_v1`'s root barrier.
4. Give this function-only transaction a distinct admitted receipt identity.
   Existing module-final/replay receipts retain their current meanings and
   must reject function-only authority. Persist new records in SDN through
   the existing cache owner; no second scheduler or cache-key family.
5. Lower the admitted function/dependency closure using the existing configured
   MIR/backend/storage owners; publish with `generic_instance_cache_publish_v1`
   only after exact object verification. Wire the current instance job's cold
   build callback to this producer; a cache hit retains current admission.

Test-first acceptance for that slice: cold cache plus no using-module MIR
must produce the same concrete signatures, rewritten calls, symbol/nominal
identity and executable result as the current scoped producer. Cover nested
generic demand and duplicate requests, changed body/configuration rejection,
missing template and wrong nominal owner, recursive-limit failure, and the
non-extractable case. Compare logical semantics separately from permitted
COMDAT placement differences. Verify no staging prerequisite remains and that
failed/incomplete publication never retires the per-module copy. Require the
exact frozen producer/source/backend receipt; authored tests cannot qualify
this transaction.

Only after cold production qualifies can a later slice replace per-module
instance body emission with verified instance references while retaining root
call rewriting. Removing that root rewrite additionally requires an admitted
call-site rewrite/relocation artifact, which PR 5518 does not supply. Global
compilation, archive root replay and linker lazy instantiation remain separate
consumers to migrate. The standalone monomorphization engine is NOT removed.
