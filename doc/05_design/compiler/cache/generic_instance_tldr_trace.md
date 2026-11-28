# Generic instance traceability through TLDR (full monomorphization, fully async)

Status: design, 2026-11-28. Docs only; no code in this lane. Base
`origin/release/1.0.0` @ `6b0b52f6f43`. TLDR: `generic_instance_tldr_trace_tldr.md`.

Inputs: owner decision D1 (full monomorphization,
`doc/05_design/language/type_system/no_any_inference_generics.md` §6, §13.1);
owner directives of 2026-11-28: instances are traceable through TLDR; generics
are **fully async on the pseudo-immutable cache + async build architecture**
(`pseudo_immutable_cache_async_build_design.md`, same directory); invalidation
and coverage are first-class.

This is an addendum to that design, not a fork of it (R01: one engine, one cache
protocol, one scheduler core). It adds **no** monomorphizer pass, cache
authority, scheduler or registry. An earlier draft of this lane had a
synchronous collector fixpoint; the owner directive supersedes it: there is no
synchronous collector step.

Markers: **[OBS]** read in the tree at the base commit; **[PROP]** proposed here.

## 1. Model in one paragraph

A generic instance is a **compile task** like a file: `InstanceTask(key)` runs
substitute -> MIR -> object inside the same scheduler and `CompileInvoker`
(fiber or process) as `CompileTask(file)`. Nothing collects instances up front.
A task that meets `Template<Args>` **requests** the instance through the
single-flight reader; the first request creates a set-once slot and starts the
task, later requests share it. An instance task requests the instances its own
body needs. The needed set of a build is whatever slots exist when the
scheduler is quiescent. Every request is recorded as a TLDR fact with its origin
span, so "who needs `Pair<i64,f64>`, why, from where" is a read, not a rebuild.

## 2. Census: where instances are needed today

### 2.1 Stages that would produce or consume a needed-instance set

| Stage | Site [OBS] | Today | Under this design |
|---|---|---|---|
| Frontend projector | `10.frontend/cache_artifact/generic_tldr_projector.spl:164` (`_project_generic_template_framed_v2`), inputs `GenericDeclInputV1` `:22-38` | projects struct/class/fn templates to `GenericTemplateEntryV1`; `body_digest` is an optional input | provider side (§3) |
| TLDR companion writer | `80.driver/cache/module_artifacts_v1.spl:258-269` (`generic-template\|` section, `generic\|` / `inline\|` body sections); decls from `module_public_summary_facts_v1.spl:157-207` | template section + body text sections written; **no per-module used-instance section** | provider + consumer sections (§3, §4) |
| HIR | `HirExprKind.Call(callee, args, type_args)` (`20.hir/generated/hir_codec.spl:3824-3848`) | explicit type args are kept on the call | request point for explicit instances |
| Types | `30.types/type_infer/generic_calls.spl`, `generalization.spl` | infers type vectors; nothing persists them as instance keys | request point for inferred instances (needs plan S2-C write-back) |
| MIR lowering | `50.mir/_MirLowering/function_lowering.spl:1947-1957` | `TypeParam` -> `MirType.i64()` (one erased body) | lowers instance bodies; no `TypeParam` allowed in |
| Driver / incremental | `80.driver/driver_build/incremental.spl:1521-1537` | a private-body edit already selects family `generic-specialization` | unchanged selection; rows now exist (§7) |
| Reverse refs | `00.common/cache/reverse_reference_facts.spl:418-422`, `reverse_reference_key.spl:46`, `80.driver/cache/reverse_reference_projection_v2.spl:80`, `reverse_reference_receipt.spl:39,56`, `cache/reference/reverse_reference_coordinator_v1.spl:809-841` | family, key and exact planner exist; `reverse_reference_register_generic_specialization_v1` has **no caller in `src`** (specs only) | first real producer (§7) |
| Object keys | `80.driver/driver_build/hir_variant_object_key_v1.spl` (module + variant digest + target id + toolchain) | per module variant; no per-instance key | per-instance key of the same shape (§6) |

### 2.2 Places that assume erasure

| Site [OBS] | Assumption |
|---|---|
| `src/compiler/50.mir/_MirLowering/function_lowering.spl:1947-1957` | "ONE ERASED BODY per generic fn"; `T` is the tagged runtime word; also `:453`, `:948`, `:1264`, `:2511` and `local_needs_erased_decode` |
| `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:314-319`, `:320-322` | active generic params, and any single uppercase letter, resolve to `TypeId::ANY` |
| `src/compiler_rust/compiler/src/pipeline_parallel.rs:39,413-415` | `PipelineStage::Monomorphize` is a label; no pass |
| `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl:44-47`, `:90` | header and `body_digest` comment: "single erased body", caller consumes signature + bound only |
| same file `:283-289` | `generic_caller_consumed_facets_v1` = [bound, signature]; `generic_template_consumed_facets_v1` = the template's **own object action** |
| `doc/04_architecture/generic_rr_hir_variant_obj.md` §2 (lines 27-38), `doc/05_design/generic_rr_hir_variant_obj.md` §1 | "erased model, one body"; body edit affects the template object only |
| `.claude/rules/language.md`, the 2026-10-31 generics plan | "Generics are erased" (plan S3-H owns these) |

Erasure wording by layer (`grep -rli 'erased\|erasure'`, files / lines):
`50.mir` 30 / 677, `35.semantics` 11 / 105, `20.hir` 20 / 83, `10.frontend`
9 / 21, `80.driver` 15 / 20, `00.common` 4 / 14, `70.backend` 8 / 13,
`95.interp` 1 / 2, `30.types` 0.

### 2.3 Stale documents found

`doc/05_design/compiler/incremental_build/generic_instance_prelink_v1.md`
describes `GenericSpecializationListV1`, `module_tldr_update_generic_spec_from_mono_v1`,
`generic_instance_build_plan_v1`, `run_file_worker_instances_v1` and
`run_monomorphization*`. **None of these symbols exists in `src`** at the base
commit (`git grep`: 0 `.spl` files; two specs still name the list type). They
went with `40.mono` (`200a05f5bc8`). Its ideas that survive here: the instance
key is `ConcreteTldrKey`; needed minus present is built before link; an
incomplete set fails closed.

Named in docs but absent in `src` (0 `.spl` files): `acquire_concrete_tldr`,
`concrete_tldr_key_for_v1`, `TraceViewProjection`, and a `generic_subst_model`
module (only the Lean model `src/verification/type_inference_compile/src/GenericSubstModel.lean`
and the `mt_key_type` key encoding used by the projector exist).

### 2.4 Counts (grep heuristics)

Method: `git grep -E` over `src/compiler`, `src/lib`, `src/app` `*.spl`.

| Measure | Count | Regex / method |
|---|---|---|
| Generic `fn` declarations | 1,067 (compiler 245, lib 745, app 77); 1,379 over all `src/**` | `^\s*(pub \|export \|static \|async \|extern \|me \|unsafe )*fn NAME<` |
| Generic type declarations | 173 lines, 146 distinct names (compiler 14, lib 143, app 16) | `^\s*(pub \|export )*(struct\|class\|enum\|trait\|union) NAME<` |
| `impl<` headers | 15 | `^\s*impl<` |
| Cross-file uses of a declared generic type, concrete args, excluding `Result` | **1,698 sites, 206 distinct `Name<args>`, 40 templates** | `NAME<...>` for the 146 names, minus uses in a declaring file, minus arg lists holding a 1-2 char uppercase binder |
| same, `Result<...>` alone | 16,918 sites, 4,018 distinct | `Result` is declared as a generic enum in `src`, so it dominates |
| Builtin-shaped (`Option\|Result\|List\|Dict\|Array\|Set\|Map\|Vec`) | 26,525 sites, 5,325 distinct | same shape; top: `Result<text,text>` 3,428 |
| Explicit type-arg calls `name<Type>(` | 251 sites, 82 distinct | declaration lines and binder-only args removed |

The plan's 1,208 [est] for explicit generic functions sits between the two
`fn` counts; the difference is scope and regex, not a disagreement.

Limits. Matching is by name, not by resolution: same-named templates in two
modules merge, aliases and re-exports are missed. "Cross-file" is not
"cross-module". The dominant case is invisible to grep: a generic function
called with inferred arguments (1,067 declarations against 251 explicit-arg call
sites), constructor calls, and `T?` / `[T]` sugar. Nested arguments count once
per outer spelling. These numbers size the problem; the instance count is still
unknown until plan S3-C's collector runs.

## 3. Provider side: the template entry

Reuse `GenericTemplateEntryV1` and the `generic-template|` section [OBS]. Two
changes, both by trailing defaulted field (the seed fills positionally) [PROP]:

1. `body_digest` keeps its field and changes meaning: digest of the template
   body that instances are built from (comment edit, plan S3-H).
2. `open_needs: [GenericOpenNeedV1]`: the instances this template's body
   requires **as a function of its own binders**. A row is
   `(callee TemplateId, [arg key], origin span, cause)`, where each arg key is
   the existing structural key (`mt_key_type` encoding) and may mention binder
   variables (`v<symbol>#<index>`). `cause` is one of `field`, `call`,
   `construct`, `bound-dispatch`. Sorted by `(TemplateId, arg keys, span)`,
   unique. `open_needs` is folded into the `generic.body` fingerprint, so a body
   edit that changes what the template needs is a body-facet change.

Substituting an instance's arguments into `open_needs` yields its concrete
needs **without opening the body**. Bodies are opened only by the instance task
that emits code.

`open_needs` is not known at parse time for inferred uses. It is a
**write-once slot** on the entry (pseudo-immutable plan C4 / S3-1): absent after
parse, filled once by the defining module's typed-HIR stage, then immutable.
"Absent" is a data state; a reader that needs it awaits the slot.

The body itself keeps travelling in the companion's `generic|` section [OBS]
(source text today; the template's `.sphb` HIR blob once S3-4 lands). An
exported generic body is therefore part of what an importer depends on
(plan S3-F), through the `generic.body` facet only.

## 4. Consumer side: the needed-instance section

New TLDR companion section `needed-instance|` per module [PROP], encoded with
the same length-framed, sorted, sealed codec as `generic-template|`:

```text
NeededInstanceV1 {
  concrete_key   # ConcreteTldrKey (concrete_tldr_key_v1) -- identity
  template_id    # TemplateId
  args_id        # ArgsId
  arg_keys       # positional structural keys, closed (no binder variable)
  origins        # sorted [(module_id, span, cause, via)]
}
NeededInstanceSetV1 { rows sorted by concrete_key, unique; complete: bool; digest }
```

`via` is empty for a direct use and the parent `concrete_key` for a need that
came from a template's `open_needs`. Only **direct** needs are stored in a
module's section; transitive ones are derived (§5) and never duplicated into
every consumer.

Rules: a row is admitted only when its view is `GENERIC_CLOSURE_CONCRETE`.
`Partial` and `Unresolved` views are IDE-only and never enter the set. A module
whose direct needs cannot all be resolved writes `complete: false`, and any
build that needs codegen from it fails closed (no silent erased fallback in
safe code). Display spellings never enter identity; spans are presentation and
trace data, outside the row digest used for invalidation.

The section is written by the consumer module's typed-HIR stage (a second
write-once slot on the module's TLDR record), not by a text scan.

## 5. Closure by async demand

There is one mechanism, the reader's single-flight slot table [OBS:
`TldrTableV1.request_async`, `tldr_table_fill_async_v1`, `CacheSingleFlightV1`]:

```text
request_instance(concrete_key, origin):
  slot = single_flight(kind = "tldr.concrete", key = concrete_key)   # set once
  append origin to the requester's needed-instance rows
  first requester only -> scheduler.submit(InstanceTask(concrete_key))
  return slot future

InstanceTask(key):
  entry  = await read_tldr(template module) -> template entry (+ open_needs slot)
  view   = concrete view (ConcreteTldrAstViewV1), must be Concrete
  for need in substitute(entry.open_needs, view.arg_keys):
      request_instance(need.key, origin = (template module, need.span, need.cause, via = key))
  body   = await template body section
  mir    = substitute + lower (no TypeParam / Infer / Any may remain)
  obj    = emit; publish packed blob + object by temp + rename
```

- **Requesters.** `CompileTask(file)` at its typed-HIR stage (one request per
  distinct direct need) and `InstanceTask` (its substituted open needs). No
  other path creates an instance.
- **Termination.** Each key has one slot, so a key is processed once. Keys grow
  only through `open_needs`; `GENERIC_INSTANTIATION_DEPTH_LIMIT` (32) [OBS]
  bounds `via` depth, and a session instance budget (count and bytes, through
  the existing cache limits) bounds breadth. Either limit makes the slot a
  terminal `Unresolved` failure naming the `via` chain.
- **Determinism.** The needed set is the least fixed point of a monotone
  function of (direct needs, `open_needs`); it does not depend on request order
  or on which requester arrived first. Three rules make the artifacts
  deterministic too: (1) the instance set of a session is **the slot table at
  quiescence, sorted by `ConcreteTldrKey`**; (2) origins are sorted, so the
  "first requester" never appears in any artifact; (3) quiescence is the
  scheduler's own rule: no runnable or parked task and zero outstanding
  `CompileTask` / `InstanceTask`. Link starts only after quiescence.
- **Failure.** A failed slot is terminal for all waiters (the
  `tldr_async_owner_integration` "required terminal failure" rule). One failed
  instance fails the link; there is no partial link set.
- **Cycles.** `A<T>` needing `B<T>` needing `A<T>` is two slots that reference
  each other's **symbols**, not each other's completion: an instance task awaits
  a callee's concrete view (signature), never its object. No await cycle exists.

The closure needs bodies of nothing: template entries, `open_needs` and
argument keys are enough. That is what "through TLDR" means here.

## 6. Ownership, dedup, keys, artifacts

**Owner [PROP].** An instance is owned by **itself**: one `InstanceTask`, one
object, named by its key. No consumer object embeds an instance body, and no
consumer module is "the" owner. The single-flight slot is the cross-module
dedup; two modules, or two processes through the daemon reader, that request
the same key share one task. Linking takes the sorted instance objects as
ordinary inputs, so no COMDAT trick is needed for correctness. Where a symbol
must be named, its name derives from `ConcreteTldrKey`, never from a requester.

**Keys.** Three levels, following the four artifact levels of the semantic
cache plan §4.3:

| Artifact | Key | Target in key? |
|---|---|---|
| Concrete TLDR view | `ConcreteTldrKey` = (TemplateId, ArgsId, constraint root, profile digest, active-guard root) [OBS] | no: target-neutral |
| Instance HIR blob (`.sphb`) | `ConcreteTldrKey` + `generic.body` fingerprint + digest of the substituted `open_needs` keys + callee signature digests | no after P-1; until then the A-1 target fold applies (hazard C1) |
| Instance MIR / object (`.spmb`, object) | the above + `hir_variant_target_id_v1` + toolchain / compiler identity (the `hir_variant_object_key_v1` shape) + lane scope | yes |

Each key is one key record with at most three algorithm-tagged digests; xxh3 is
a lookup hint only; compact 16/32-bit ids are session handles, never identity.

**Artifacts.** Packed pseudo-immutable blobs read in place by mmap, published
once by temp + rename, counted by the daemon usage ledger against the
per-source limits (the "source" of an instance is its template's module).
`BuildSession` frees an instance's HIR and MIR after its object is emitted; no
GC. No lock is taken anywhere: slots are set-once, publication is
compare-and-rename, coordination is the scheduler's message passing
(`doc/04_architecture/language/concurrency/concurrency_architecture.md`).

## 7. Reverse references and invalidation

One family, `generic-specialization` [OBS], gains its first producer. Rows are
written by the task that performed the read, through the existing
`reverse_reference_register_generic_specialization_v1`:

| Row (definition -> consumer) | Written by | Meaning |
|---|---|---|
| template facet `generic.body` -> instance key | `InstanceTask` | the instance was built from this body |
| template facets `generic.signature`, `generic.bound` -> instance key | `InstanceTask` | |
| template facets `generic.signature`, `generic.bound` -> consumer module object action | `CompileTask` | unchanged from the erased design |
| instance key -> requester (module object action, or parent instance key) | requester | the trace edge; also "who links this symbol" |

Under erasure a body edit dirtied one template object. Now `generic.body` is
consumed by N instance actions. A consumer **module** still does not read the
body (`generic_caller_consumed_facets_v1` stays [bound, signature]); it reads
the instance's symbol. So the exact dirty sets are:

| Change | Dirty | Not dirty (negative control) |
|---|---|---|
| nothing | nothing: zero instance tasks run, zero links | every instance object |
| template body (same `open_needs`) | all instance objects of that template, for the targets built; relink | consumer module objects; instances of other templates |
| template body, `open_needs` changed | the above + newly needed instances built; instances no longer needed leave the link set | their cached blobs stay valid until evicted |
| template signature or bound | instances of that template + every consumer module with that edge (their `ConcreteTldrKey`s change through TemplateId) | unrelated templates |
| a consumer changes an argument (`Box<i64>` -> `Box<f64>`) | that consumer's object; the new key built on a miss, shared on a hit | the old instance object stays valid for other consumers |
| needed set of a module changes, no template change | only instances whose key is new to the build; relink | every existing instance object |
| target, toolchain or lane changes | MIR / object level of every instance | concrete views and (after P-1) HIR blobs |
| argument type's own definition changes (a struct used as `T` gains a field) | instances whose arg keys or callee signature digests include it | instances over other arguments |
| private non-generic body in the template's module | nothing generic | all instances (plan S3-F acceptance) |

Planning reuses `plan_generic_invalidation_v1` [OBS]; only the consumer
population changes. An RR shard that is incomplete or fails to decode gives the
existing fail-closed fallback (rebuild the affected module set), never a
narrower guess. `incremental.spl:1536` already selects this family on a
private-body edit; with rows present that selection becomes exact.

## 8. Traceability queries

Facts, all already in the section and the RR rows: template, arguments, origin
`(module, span, cause)`, `via` chain, instance object key per target.

| Query | Answer from |
|---|---|
| who needs `Pair<i64,f64>` | RR rows instance -> requester |
| why | `cause` + `via` chain up to a direct use in source |
| from where | origin spans |
| what does this template cost | instances per TemplateId, with object bytes from the ledger (feeds plan S3-C / S3-G reports) |
| what does an edit to this body rebuild | `plan_generic_invalidation_v1` dry run |

Surface: these are attributable facts for the single `TraceViewProjection` of
`doc/04_architecture/extreme_typing_traceability.md`, which serves CLI, LSP, MCP
and reports. **That projection is not implemented** (0 `.spl` files). Until it
is, the facts are readable only through the RR receipt and the section codec;
this design adds no CLI or second query authority of its own.

## 9. Guards

- No `TypeParam`, `Infer` or `Any` reaches MIR from safe code: checked on every
  instance body after substitution (plan S3-D verifier), failing the slot.
- `Partial` / `Unresolved` views are never codegen input; an `Unresolved`
  request is a diagnostic at its origin span.
- Depth 32 on `via`; session instance budget; the T3 cap (plan S3-A) applies to
  implicit generics before a request is made.
- An unknown digest algorithm, a foreign slot reference, or a corrupt section is
  a miss or a terminal failure, never a hit.
- Polymorphic recursion is refused by plan S3-B; the depth limit is the backstop.

## 10. Remote execution

An `InstanceTask` is a content-keyed build action in the sense of
`doc/04_architecture/dist_build_scheduler.md`: its action key is the instance
object key of §6 and excludes node, attempt, priority and scratch path. The
async local runner or the distributed scheduler may run it remotely under the
existing attempt lease and monotonic publication fence; a delayed worker cannot
publish against an old fence.

Inputs a remote worker needs (`InputManifest`), all immutable and digest-named:
the template's TLDR entry with `open_needs`; the template body section (or its
`.sphb`); the closed argument keys; the TLDR entries the body reads (callee
signatures, argument type layouts); target context; toolchain manifest. **No
full source tree.** Discovery (requests) stays on the scheduler side: a remote
worker returns its substituted needs in the result candidate and the parent
submits them, so slots are created by one authority.

Acceptance: the same instance built locally and remotely yields byte-identical
objects.

## 11. Seed scope

Per D4 and open Q13 the Rust seed is syntactic only. It keeps
`type_resolver.rs:314-322` and one erased body, writes no `open_needs` and no
`needed-instance|` section, runs no `InstanceTask`, and does not read these
sections. Seed-built stage 1 is therefore erased; instances exist from the
first self-hosted build on. If Q13 is later answered "the seed monomorphizes"
(plan S3-E), it must produce the same `ConcreteTldrKey`s; nothing else here
changes.

## 12. What is landed and what this design needs

Verified by `git grep` over `src/**/*.spl` at the base commit, not from
document status.

| Needed piece | In `src`? | Plan step |
|---|---|---|
| Template entry, section codec v1 / v2, `ConcreteTldrKey`, facets | yes | - |
| `TldrTableV1.request_async`, `tldr_table_fill_async_v1`, `SourceReader.read_src_async` | yes | - |
| `CacheSingleFlightV1` | yes (daemon and AOP match cache; not on the compile path) | S1-5 |
| `mir_cfg_select_arm`, `hir_variant_object_key_v1` | yes | P-1 |
| `plan_generic_invalidation_v1`, RR family and receipt | yes; register helper uncalled | - |
| `parse_async` / `lower_hir_async` / `lower_mir_async` / `emit_object_async` | **no** | S1-1, S1-2 |
| `read_tldr_async` | **no** | S1-3 |
| `trait CompileInvoker`, `FiberInvoker` | **no** | S2-1 |
| `KeyRecordV2` | **no** | S2-6 |
| Write-once slot type, `.sphb`, `.spmb` | **no** (`.spab` only) | S3-1..S3-4 |
| Daemon usage ledger | **no** | S3-5 |
| Concrete-view acquisition (`acquire_concrete_tldr`) | **no** (doc only) | F2 below |
| `TraceViewProjection` | **no** (doc only) | extreme-typing lane |
| `generic_subst_model` (the one substitution implementation) | **no**: it was `40.mono/model/generic_subst_model.spl`, deleted with the stage; only its Lean model and the `mt_key_type` encoding remain | S3-F4 restores that one file, not the stage |
| Instance naming, per-task output invariant | **no** | S3-F4 |

Conflicts to resolve before implementation:

1. `doc/03_plan/compiler/cache/tldr_async_owner_integration_2026-10-30.md`
   forbids editing "mono semantics" in that slice and its runtime evidence is
   UNRUN. Instance requests extend that table's key space; the slice's API is
   reused, its exclusion needs lifting by its owner.
2. `tldr_caller_async_prerequisites_2026-10-30.md` lists five blocking
   prerequisites for any real async caller (carrier token adapter, cumulative
   bounds, terminal shutdown, preserved result, worker retention). Instance
   tasks are such a caller, so they inherit all five.
3. Flag name drift: the design says `SIMPLE_HIR_TARGET_NEUTRAL`; the code uses
   `SIMPLE_HIR_CFG_SELECT` (6 `.spl` files).
4. The pseudo-immutable plan marks packed HIR/MIR blobs as work to do; until
   S3-4, instance artifacts can only be objects plus the concrete view.

## 13. Sub-stages

Listed with dependencies and acceptance in
`doc/03_plan/language/type_system/no_any_inference_plan.md` (S3-F1..F10) and
slotted into the waves of
`doc/03_plan/compiler/cache/pseudo_immutable_cache_impl_plan.md` §5.

## 14. Coverage gates

Targets (owner, 2026-11-28): **>= 95 %** per touched unit module from its unit
specs; **>= 70 %** over the module set (generic instance, async, TLDR trace,
invalidation) from unit + integration + system specs.

Measured on this host, 2026-11-28, seed
`C:/dev/keep/seeds/simple-local-20261128f.exe` (40,430,592 bytes),
`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<file> SIMPLE_EXECUTION_MODE=interpreter
<seed> run test/01_unit/compiler/cache/coverage/generic_tldr_view_v1_mcdc_spec.spl`:
the run works and writes an SDN report. Findings:

- **Line percentage per module cannot be computed from the report.** The
  `lines |file, line, hit_count|` table lists hit lines only (375 rows, 0 with
  hit count 0; summary `total_lines` = `covered_lines` = 375). There is no line
  denominator. The `functions` table has the same shape.
- **Decision and condition tables do have a per-file denominator** (every site
  is registered at load): for `generic_tldr_view_v1.spl` this run shows 130
  decisions (24 covered) and 87 conditions (19 covered), with 131 hit lines.
- The spec itself is **red under this seed: 26 of 59 examples fail** (for
  example "expected unsupported entry schema to equal bad bound"), which is why
  the covered counts are low. That is an existing defect to fix first (F10).
- `bin/simple test --coverage` cannot be used under the seed (needs the
  self-hosted child APK receipt, `doc/07_guide/infra/testing/coverage.md`).

Smallest gate that works today [PROP]: one script modelled on
`scripts/check/check-hash-algos-coverage.shs` that runs the listed specs with
`SIMPLE_COVERAGE=1`, and per target file computes **decision coverage** from the
SDN (`covered / total`, both-outcomes rule), failing below 95 % for a unit
module and below 70 % for the set total; a spec failure or an empty denominator
is an ERROR, not a pass. Decision coverage is the stricter measure, so it is a
safe stand-in. To gate on **lines** as the owner wrote it, the interpreter
must register line sites with zero counts at module load, as it already does
for decisions (`interpreter/coverage_sites.rs`): a small seed change, listed as
an owner decision. The script and the module list are shared with the sibling
aspect lane; neither lane forks them.
