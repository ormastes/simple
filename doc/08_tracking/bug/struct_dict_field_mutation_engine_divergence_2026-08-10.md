# Dict-in-struct field mutation through a by-value receiver DIVERGES BY ENGINE

> **REPRODUCED 2026-08-17**, and root-caused. `test/01_unit/compiler/interpreter/self_field_assign_spec.spl`:
> `✗ preserves self.field mutations passed through free functions — expected 1 to equal 11`
> `✗ preserves struct dictionary-field mutations through returning free functions`
> `Results: 13 total, 11 passed, 2 failed` (executed=13, dropped=0).
> The controlled pair: the ARGUMENT-boundary sibling
> `✓ preserves dictionary-field mutations through free functions` passes while the
> RETURN-boundary case fails. Shared cause with
> `enum_payload_dict_copied_on_function_return_2026-07-28`; see
> `interpreter_return_boundary_never_merges_shared_collections_2026-08-17.md`.


- **Status:** OPEN — engine divergence (defect) + undocumented language semantics (design question)
- **Filed:** 2026-08-10
- **Supersedes the framing of:** `struct_field_dict_mutation_through_free_function_is_a_noop_2026-08-10.md`
  (that report is correct about the interpreter, but concluded "value semantics,
  so the write is discarded" from ONE engine. Two of three engines disagree.)

## Measured, one probe, three engines, with an absence control

Probe: `class MutableDictHolder` / `struct MutableStructDictHolder`, each with a
`values: Dict<text, i32>` field, each written through a free function taking the
holder by value as `self` and doing `self.values[key] = next`. Every reading
assertion is paired with an **absence control** (`has("never-written")`), so a
dict that answers `true` to everything cannot fake a pass.

| engine | invocation | CLASS has("answer") | STRUCT has("answer") | absence control (both) |
|---|---|---|---|---|
| interpreter | `SIMPLE_EXECUTION_MODE=interpreter bin/simple run` | `true` | **`false`** | `false` (correct) |
| JIT | `SIMPLE_EXECUTION_MODE=jit bin/simple run` | `true` | **`true`** | `false` (correct) |
| native/AOT | `bin/simple native-build -o … && ./…` | `true` | **`true`** | `false` (correct) |

The absence control is correct in all three engines, so no engine is trivially
answering `true`; the STRUCT column is a real behavioural split.

**This is engine divergence and it is a defect regardless of which semantics are
intended.** Whatever Simple decides `struct` + `Dict` field means, all three
engines must mean the same thing. Today, identical source silently produces
opposite state depending on the lane it runs in — the worst possible failure
mode, since it is invisible to any positive assertion.

Consistent with the already-filed
`doc/08_tracking/bug/jit_struct_assignment_aliases_not_copies_2026-08-10.md`
and `doc/07_guide/language/value_semantics_by_engine.md:31-33`
("Structs copy in the interpreter but ALIAS in the JIT"). This report extends
that known split to **collection-valued fields** and to the **native/AOT** lane,
which that doc did not cover.

## Intended semantics: UNDOCUMENTED

Documentation search result (doc/02_requirements, doc/04_architecture,
doc/05_design, doc/07_guide, .claude/memory):

- The **basic rule IS documented**: `doc/02_requirements/language/types/structs.md:45`
  "Structs are value types (copied by default)"; `doc/07_guide/language/syntax.md:456,460`
  labels `struct` value / `class` reference.
- `doc/04_architecture/adr/ADR-004-indexed-access-value-semantics.md:22-24` makes
  value semantics "the language contract" for **indexed access**, and names
  write-back as the only portable mutation form.
- **The specific question is UNDOCUMENTED**: no document states whether copying a
  struct **deep-copies an embedded Dict/List or shares the handle**. The nearest
  statement, `doc/07_guide/language/value_semantics_by_engine.md:21-23`, says
  `AggregateCopy` is SHALLOW for a **struct-typed** field only, and `:75-79`
  explicitly hedges: dict propagation reports "are consistent with dicts being
  reference-backed containers in at least some lanes" — unmeasured.

So the copy DEPTH for collection-valued struct fields has never been decided.

## Design question — NOT decided here

Two candidate resolutions, both self-consistent:

**(A) Deep — a struct copy deep-copies its Dict/List fields.**
Matches "struct is a value type" literally and makes ADR-004 uniform: a struct is
wholly a value. The interpreter is then RIGHT and JIT/native are wrong.
Cost: silent O(n) copies on every struct pass; a struct holding a large Dict
becomes an expensive parameter. Existing code that reads as "handle in a record"
gets a performance cliff with no syntax marking it.

**(B) Shallow — the struct copies, the Dict field is a shared handle.**
Matches the measured `AggregateCopy` implementation and the JIT/native lanes, and
keeps struct passing O(fields). Cost: `struct` stops meaning "value type" in the
way the docs claim — a struct with a Dict field is a partially-reference value,
which is exactly the footgun that produced this bug.

**Recommendation (not a ruling):** **(B) shallow**, made EXPLICIT in the docs and
enforced by fixing the interpreter to match, *plus* a compiler diagnostic on
scalar-field mutation through a by-value struct param (which genuinely is a
no-op under all three engines and has no defensible reading). (B) is what two of
three engines already do and what the runtime is built for; (A) would be a
performance regression across the whole compiler. But this is a language-design
call with repo-wide consequences and it is **not mine to make unilaterally** —
per the repo rule, filed rather than picked.

## Spec status: deliberately left RED

`test/unit/compiler/interpreter/self_field_assign_spec.spl` and
`test/01_unit/compiler/interpreter/self_field_assign_spec.spl` — example
`preserves struct dictionary-field mutations through returning free functions`
remains RED. It was NOT softened, marked pending, or deleted. It is a
correctly-failing spec pinning an undecided contract, and it now additionally
documents an engine split. Unblock condition: resolve (A) or (B) above, make all
three engines agree, then this example goes green (under A) or is rewritten to
assert shared-handle propagation (under B) — with its absence control intact
either way.

## Blast radius — production sites (engine-conditional)

Sweep of `src/**` (vendor excluded) for collection-valued field mutation through
a by-value `struct` receiver/parameter. Simple has an explicit `mut` param
marker, so its absence is meaningful. 114 mutation sites found in fns taking such
a struct as a param; **104 are by-value**.

**Critical caveat, and it is the reason this table is not a defect list:** these
sites are no-ops **only under the interpreter**. Under JIT and native they alias
and work. So each is a *latent* defect that fires when the lane changes — and
scalar-field mutations at the same sites (e.g. `_next_lease_id`) are no-ops in
**every** engine.

| site | struct | mutator / field | classification |
|---|---|---|---|
| ~~`src/lib/nogc_sync_mut/service/lease_manager.spl:126,152`~~ | `LeaseManager` | `try_acquire_{exclusive,shared}` → `leases.push` | **FIXED 2026-08-10** (`ba00d1781eb`) — `LeaseManager` is now a `class`. |
| ~~`src/lib/nogc_sync_mut/service/lease_manager.spl:47`~~ | `LeaseManager` | `_next_lease_id` → `next_id` (**scalar**) | **FIXED 2026-08-10** (`ba00d1781eb`). Correction to this report: the "no-op in ALL engines" claim held for the interpreter but **not** for the JIT — measured `build/q18/probe_semantics.spl` under a real (non-fallback) JIT, the pre-fix struct shape yielded distinct ids and a working BUSY branch, because the JIT aliases the struct. Interpreter: `lease-1, lease-1`. JIT: `lease-1, BUSY`. |
| ~~`src/lib/nogc_sync_mut/service/lease_manager.spl:76,168`~~ | `LeaseManager` | `_reclaim_ghosts`, `release_lease` → `leases = kept` | **FIXED 2026-08-10** (`ba00d1781eb`) |
| `src/app/sj_daemon/request_handler.spl:66-72` | — | consequence | **PARTLY FIXED 2026-08-10.** Unreachability of `exit_code: 75i64` proven by execution (`C.req1_acquired=true C.leases_visible_to_handler=0 C.req2_exit=0`, negative control 0) and now reachable when the handler is held directly (`C.req2_exit=75`). Still unreachable **through `SjClient`**, for a different reason: `interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10.md`. Spec `test/{02_integration,integration}/app/sj_daemon_mutual_exclusion_spec.spl` is 4/5 green with that one example deliberately RED. |
| `src/lib/nogc_sync_mut/service/request_queue.spl:43,45,58,67,98,99` | `RequestQueue` | `enqueue`, `dequeue`, `queue_drain` | **DEAD as production code, but NOT unreferenced** — correction to this report. Verified with `/usr/bin/grep -rn` (positive control: `lease_manager_new`, 40 hits outside its module). Three live references remain: `service/daemon_base.spl:34,44` constructs a `queue: RequestQueue` field that is never read; `test/{01_unit,unit}/lib/service/request_queue_spec.spl` (92 lines each, byte-identical); and `test/{01_unit,unit}/app/mcp_unit/mcp_analysis_tools_spec.spl` uses the module as a **live MCP-search fixture** (`PROBE_FILE`, plus assertions on the literal strings `fn request_queue_new`, `struct RequestQueue`, `queue_drain`). Deleting the module therefore REROUTES the MCP analysis spec into RED unless its fixture is repointed first. |
| `src/compiler/99.loader/loader/module_loader.spl:247,306,476,505,787-803` | `ModuleLoader` | load / replace_live / unload | latent, interp-only (16 sites) |
| `src/app/gc/core.spl:192,330,341-356,411` | `GCCore` | allocate / sweep / root reg | latent; caller `src/app/gc/mod.spl:71` discards the result |
| `src/os/services/nvfs/core/pmap_btree.spl:123,277,342,506-795` | `PmapBTree` | node alloc / split / insert / delete | latent, interp-only (7 sites) |
| `src/compiler/10.frontend/core/hir_types.spl:128-133` | `CoreSymbolTable` | `symtab_add` → 6 parallel arrays | latent, interp-only |
| `src/compiler/80.driver/cache/tier_router/tier_router.spl:130,175` | `TierRouter` | memo cache | latent — cache silently never populates under interp |
| also | — | — | `99.loader/loader/{generation_sweeper.spl:65,103,133, smf_cache_manager.spl:39,52,65, object_provider.spl:79,95}`, `module_resolver/types.spl:473,491`, `80.driver/shb/shb_extractor.spl:171,187,307`, `lib/nogc_async_mut/{mailbox.spl:32,47,70, gen_event.spl:50,59, process_set/config.spl:96,113,130}`, `lib/nogc_sync_mut/{sfm/di_bridge.spl:53,54, database/fts.spl:114}` (+ nogc_async twin `:111`), `os/kernel/arch/common/interrupt_dispatch.spl:44,50`, `os/kernel/log/klog.spl:86`, `app/vscode_extension/src/{diagnostics_provider.spl:69,79,83, code_actions_provider.spl:86,90}`, `app/interpreter/helpers/debug_simple.spl:139,146`, `compiler/70.backend/backend/optimization_passes.spl:97,114` |

Benign (mutation feeds a returned new value, not a no-op):
`compiler/35.semantics/macro_check/hygiene.spl:66`,
`compiler/60.mir_opt/.../pattern_rule_pass.spl:355`,
`lib/common/experiment/artifact.spl:71,94`,
`lib/common/structural/layout/scheduler.spl:32`, `lib/editor/view/tab.spl:20`,
and the `mimalloc_page/page_policy/secure.spl:55/37/31` triplets.

## Runnable check left behind

`test/unit/compiler/interpreter/self_field_assign_spec.spl` (RED, deliberate)
plus the three-engine probe recipe in the table above, which is reproducible from
this file in under a minute and is the only form that catches the divergence —
a single-engine run cannot.
