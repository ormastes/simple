# Node attributes: current implementation and reuse audit

Date: 2026-11-06. Inspected revision: `5476552cc1b343b7d58e439ad468490e4dae91ef`.
Status: source inspection only; no compiler, SSpec, benchmark, or XRay run.

## Request and scope

The user selected **full node-attribute support**, asked for structural changes
first, then explicitly requested that architecture/design land first for sharing.
The feature must be applied to Simple itself. The requested off switch is treated
as an explicit build-time opt-in, not a switch that removes safety from live nodes.
The [consolidated plan](../../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md)
remains the upstream specification. A small pilot is a delivery stage, not the
definition of completion.

## Existing implementation versus missing integration

| Capability | Source evidence | Finding |
|---|---|---|
| AST columns and owner accessors | `src/compiler/10.frontend/core/_AstExpr/nodes.spl`, `expr_owner_*` | Existing SoA-like arrays must remain owner-private; the source explicitly warns about copied arrays across module boundaries. |
| AST generation diagnostics | Same owner, `ast_generation`, `ast_gen_check_index` | Existing diagnostics are not a qualified ready/pending or slot-lifetime contract. |
| Canonical physical layouts | `src/lib/common/structural/storage_layout/storage_layout_contracts.spl` | Reuse `StorageLayoutPlanV1`; do not add a competing layout enum. |
| Shared structural identities/tags | `src/lib/common/structural/identity/entity_id.spl`, `tagmap/tag_schema.spl` | Frozen structural metadata contracts exist. TagMap's fixed value-kind inventory is not arbitrary nominal language field typing. Do not mutate its V1 format to pretend otherwise. |
| Adaptive storage | `src/lib/nogc_sync_mut/src/collections/adaptive_map.spl` | Existing collection machinery is an integration input, not a managed-node schema implementation. |
| HIR field metadata | `src/compiler/20.hir/hir_definitions.spl`, `HirField` | Extend logical field metadata while preserving visibility and physical constraints. |
| Rust implicit getters | `src/compiler_rust/compiler/src/interpreter/expr/calls.rs` | Existing real-field/getter conventions; not generated storage-backed node access. |
| Pure-Simple field evaluation | `src/compiler/10.frontend/core/interpreter/eval_access.spl`, `_EvalOps/access_literal_assign_eval.spl` | Indexed/linear field lookup exists. Both paths need managed-place integration. Assignment expression evaluates RHS before receiver in the inspected active helper. |
| Field aspects | `src/compiler/10.frontend/core/aop_predicate_parser.spl` | `get` and `set` are explicitly E1507-deferred. |
| Annotation pointcuts | `src/compiler/10.frontend/core/aop.spl`, `aop_pointcut_eval_selector` | Tokenized `attr(...)` falls through to false; a separate older matcher is not end-to-end support. |
| Managed node schema and construction | Searches across owned SPL/Rust sources for `node_tree`, `NotInit`, `TreeSchemaId`, `AttrRead`, `AttrWrite`, `AttrKey`, `node_attribute`, `data_schema` | No integrated implementation found. Hits were unrelated UI trees, initialization-error names, platform attributes, or database schemas. Negative search evidence is supported by the concrete missing evaluator/AOP paths above. |

The exact-title PR search for `node attribute` and open `data schema` PRs returned
no matches at inspection time. This is not proof that no unpublished work exists.
Implementation uses an isolated worktree and must recheck relevant paths before
each landing. Vendored runtime/compiler sources were excluded from the audit.

## Qualification environment

The primary Windows workspace had no `bin/release/**/simple.exe` and no admitted
Stage 2/3 receipt discovered in the inspected build locations. Available files
included `bin/simple.exe` and a C-bootstrap executable, whose presence alone does
not establish self-hosted admission. The Windows wrapper can select Rust binaries;
it must not be used as an implicit test fallback. Production verification remains
pending until an admitted runtime is available or built through the canonical
bootstrap route. This limits execution evidence, not architecture authoring.

## Research boundary

The supplied report already contains domain research, pinned sources, and prior
plan reconciliation. This audit adds current local evidence; it does not claim to
have revalidated external references or CI results. Full integration is **not
already implemented**, while substantial storage and compiler infrastructure is.

## Release branch follow-up

The user subsequently selected `release/1.0.0` as the implementation/landing base.
The release inspection pin is `e2ce7042552176e9a8fd8f79505faec2e4f06f14`.
Its AST owner has additional changes, which are preserved. The field-selector
validator still explicitly rejects get/set with E1507, and targeted searches of
compiler common/frontend and structural owners found no managed-node schema or
whole-node builder implementation.

This branch already contains `src/lib/common/trace/observer_contract_v1.spl`
(`TraceObserverV1`), session/config/codec/map owners and LLVM/native leaves under
`src/lib/nogc_sync_mut/trace/`. Integration must extend these existing contracts
through their version/capability mechanism, not introduce the facade from scratch
or renumber existing events. Their source presence is not executed node-event
qualification. The main-branch audit above remains historical evidence.

An additional installed executable at
`C:/Users/ormas/dev/simple/bin/release/x86_64-pc-windows-msvc/simple.exe` was
inspected with `--version`. SHA-256:
`6094dcae291aa984973ccd681f956e67a7a60543ab99f76a29313fbbfdee96d1`.
It explicitly reports a Rust bootstrap-seed warning. No feature tests were run
with it; the release-directory name does not establish self-hosted admission.
