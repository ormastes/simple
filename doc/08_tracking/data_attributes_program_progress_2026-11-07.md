# Unified attributes, layouts and XRay: finite delivery matrix

## V3 canonical type follow-up (source draft)

V2 structural PR [#7561](https://github.com/ormastes/simple/pull/7561) merged as
`9f7c614fe06e66b16c965840525b7b08e6255069`; its 25 cases remain UNEXECUTED.
The next [rich type resolver package](../05_design/compiler/data_schema_v3_exact_type_reducer.md)
uses the separately owned semantic type codec/HIR adapter, a private shared
normalized reducer, shared property checking and one versioned SDN normalizer.
It preserves V1/V2 public outputs/digests and adds a distinct V3 rich surface.

Implementation/test source is approved by Astra; runtime qualification pending.
The dedicated V3 decoder returns explicitly unbound type expressions. Actual
source/config binding and frozen consumer contexts remain the assigned W1b lane;
transport fixtures do not finish that work. Lifecycle/storage/observation and
three-family/native/BuildRunner gates below remain part of the accepted scope.
No work package becomes complete solely because a richer schema record exists.

Date: 2026-11-07. Accepted scope remains the
[consolidated program](../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md)
and [selected node requirements](../02_requirements/feature/node_attributes.md).
This file tracks bounded work, not a reduced replacement scope.

## Existing source baseline

Audit baseline: release `98669e12655ab2be54aec09acc118aeb43ee8ff0`.
Retain the landed canonical schema/resolver foundation (`c09d8392cac`, #7220),
construction facts (`3dc26c9c3d5`), reference storage pilot (`9b27558ef06`),
collection adapter foundation (`bb40625fd0e`) and data aggregation/profile work
(`c850d933f80`). They are inputs to integration, not proof of full runtime support.
HIR access-site work (`5a48dc6d48c`, `eab5f542b48`) adds a postpass side table
(`HirAttrAccessV1`, `attr_access_sites.spl`); it does not itself lower managed
places or change MIR. Reuse its canonical site identities instead of adding a
second collector.

## Package matrix and exit evidence

| Package | Required next result | Current qualification |
|---|---|---|
| W0/W1a | Extend existing schema owner with explicit views/property contracts, V2 digest, SPL/SDN equivalence and conflict refusal | V2 source and 25 unit examples approved by Astra, including UTF-8 byte bounds; execution UNEXECUTED |
| W1b | Frontend extraction, exact language type/symbol binding including qualifiers, source/config authority, off/enabled mode, driver freeze and one LSP surface | Remaining integration; no PASS claimed. 2026-11-13: storage-mechanism resolver `data_attr_storage_resolve_v1` landed with the SPL tag reader (`@node_tree` class + `@attr_storage`) in `node_view_gen`; `data_schema_resolver_spec` 10/10 GREEN (interpreter lane) |
| W2a | Reuse existing HIR site identity for real AttrRead/Write places, evaluation order, nested writes, moves, borrows and logical event identity | Site side table already landed; places/lowering remain |
| W2b | Must-resolve construction, executed default commits/retry, cleanup, readiness and interpreter parity | V1 facts landed; no compiler/runtime enforcement proof. **Sub-plan P1** (effective-public definite-initialization verifier → `E_ATTR_REQUIRED_UNINIT` / `E_ASYNC_INIT_MISSING` / `E_ASYNC_INIT_UNSUPPORTED`, behind the §4.3 migration-warning gate with an offender census; ASY-03/04/05, ATTR-01/04) and **P3** (async registered init on the write-once `phase_cell_*_v1` cells of the node-storage lane; ASY-01/02/06/07/08) land here. Immview lane; it consumes `node_construction_*_v1` facts and does not edit `node_lifecycle_contracts.spl` |
| W2c (added 2026-11-13) | `Immutable<T>` live read-only projection (IMM-01/02), then `RevisionImmutable<T>`/`FrozenImmutable<T>` with W8 cache identity (IMM-03/04, REV-01/02); contract in the [sub-plan](../03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md) §2 | Not started; grammar for `Immutable<T>` unverified until P0 probes |
| W3b | Extend existing read pilot through actual writes/construction/retirement and sparse/direct/column exact-value/presence parity | Pilot source exists; broader runtime integration remains. 2026-11-13: storage mechanism per attribute switchable by tag or SDN rule; committed pilot reads `op` through a generated column and `inferred_type` through the sparse hash store with value parity against the AST pool owner (`ast_node_pool_pilot_spec` 6/6 GREEN). Phase B: design note `doc/05_design/compiler/data/node_tree_storage.md` with measured bytes per node (bridge 1.3-1.5 KB/AST node on a cold heap, HIR blob 157-183 B/node) and per-(phase, module) write-once cells (`node_lifecycle_contracts_spec` 14/14). Sub-plan P4 (one `AttributeSchema` over embedded/SoA/sparse-hash) = node-storage lane |
| W4b | Apply existing CollectionPlan/adaptive adapter at real source sites with exact result/order/refusal evidence | Foundation landed; source-site integration remains |
| W5b | Bind existing data record/aggregation/profile path to admitted logical emitters and one correlated session/coverage/loss identity | Prior record/profile source exists; emitters/integration remain. Sub-plan P5 (static profile-guided `StoragePolicyId`, PROF-01) spans W5b/W6/W7 |
| W6 | Three-family reference workload, report-only plan, exact next-instance/next-build results and cost/peak-memory report | Depends on W3b–W5b; no combined evidence |
| W7 | Qualified native source bindings and field widths/layouts plus XRay on the same workload and provider/backend combination | Depends on reference result and admitted backend/provider evidence |
| W8 | BuildRunner contexts, cache semantic/physical invalidation, transfer/ownership and LSP adoption | Existing owners retained; adoption evidence remains |
| W9 | Transactional shared live migration, budgets, failure retention and lease/reclamation checks | Deferred under original W6–W8/progress gates. Sub-plan P6 (`ContainerPolicy.selection = runtime`, PROF-02/03) inherits the deferral |
| W10 | Staged provider/platform expansion under the existing shared trace contract | Original platform/evidence gates retained; no Windows/GPU inference |

Every package must record producer path/hash/stage/admission, source revision,
target/backend/provider, actual test inventories/counts, commands, exits and
artifacts when executed. Authored examples, reviewed source and executed runtime
evidence remain different states. Missing runtime never becomes a seed fallback.

## W0/W1a ownership and verification

Implementation: Sol. Architecture and final source review: Astra. Merge owner:
root/packaging through reviewed release PR. Additional sidecars: N/A for this slice.
Owner paths: the three `src/compiler/00.common/data/*_v2.spl` modules and
`test/01_unit/compiler/data/data_schema_resolver_v2_spec.spl`; no frozen V1 edits.

The [detail design](../05_design/compiler/data_schema_v2_contract_extension.md)
records exact semantics and limits. The [input guide](../07_guide/compiler/data_schema_v2_input.md)
describes a dedicated structural API, not shipped driver configuration support.
The [manual](../06_spec/01_unit/compiler/data/data_schema_resolver_v2_spec.md) is
manually maintained with execution/docgen/maintenance explicitly pending.

No full W0/W1, generated accessor, lifecycle, storage, AOP, profile integration,
native layout, BuildRunner adoption or whole-project completion is claimed by
this contract extension. The runtime qualification gate remains open.

## Immutable views / async initialization sub-plan (bound 2026-11-13)

Plan: [`immutable_views_async_init_revisions_2026-11-13.md`](../03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md)
(its §0a holds the phase → package map; this file does not repeat it).
Pin: `origin/release/1.0.0` @ `9100f50e680`. Lane: `work/immutable-views-async-init-20261113`.

| Step | Deliverable | State |
|---|---|---|
| P0 inventory | [symbol-to-requirement map + parser probes](../05_design/compiler/data/immutable_views_async_init_p0_inventory_2026-11-13.md) (`doc/08_tracking/` root is over the fan-out limit, so the map lives under `doc/05_design/compiler/data/`) | done 2026-11-13: no contract implemented; `async <expr>` ctor argument does not parse; `Immutable<T>`/`@support_async_immutable` accepted only by lenience; missing required field is nil/0-filled (`lower_struct_construct`), E1007 unused |
| P1 verifier | SSpec ASY-03/04/05, ATTR-01/04 RED → GREEN; verifier as report over `src/compiler`+`src/lib`+`src/app`; offender count decides gate (warning / opt-in vs error) | landed on lane, under review: verifier `12bce06467a`; struct-update-spread false positive fixed and gate modes specified in `d9faba71fd8` (spec 12/12; RED 11/12 before the fix). Gate `SIMPLE_REQUIRED_INIT_CHECK` defaults to `off` because the census is non-zero. Partial census at 14:30 KST: 366 compiler files, 13 rows, 6 sites, 4 classes, all the omitted `has_<f>` flag of a `# DESUGARED` optional pair. lib/app still running. Detail in plan §0a "P1 census and gate" |
| P2 `Immutable<T>` | IMM-01/02; then revision/frozen handles | pending, after P1 review |
| P3 async-init gate | ASY-01/02/06/07/08 on `phase_cell_*_v1`; reference API `f8db9920671` landed on `release/1.0.0` via #8829 (`04f02062860`), so no longer blocked | pending, after P1 review |

Authored plan text, reviewed source and executed runtime evidence remain
different states; nothing above is complete because the plan exists.
