# Architecture: macro reverse-reference invalidation

**Lane:** `macro-rr-invalidation` (2026-11-01). **Research:** `doc/01_research/local/macro_rr_invalidation.md`. **Shared RR contract:** `doc/03_plan/compiler/generics/generics_refactoring_formal_verification_plan_2026-10-31.md` §8. **Sibling:** `generic-rr` lane — both lanes use one RR key/edge model (§2); neither forks it.

Status: design contract; runtime qualification UNRUN until a self-hosted `bin/release/<triple>/simple` exists on this host.

## 1. Problem and non-negotiables

Production facts (read on `origin/release/1.0.0@8a935437a98`, see research §2–§3):

1. Macros are parser-side facts only: `parse_macro_decl` fills `macro_fact_def_*` pools and `name!(args)` is parsed as an ordinary call; no owner expands macros at build time. The projector (`10.frontend/cache_artifact/macro_reference_projector.spl`) predicts generated public names from the contract.
2. The legacy `.rr` receipt (`80.driver/driver_build/incremental.spl:783`) publishes schema 1 with **no macro family**; the consumer loop (`:1105`) queries macro families anyway, so every edit widens to the complete inventory. The only macro→forward-manifest bridge was deleted with `generic_spec_rr_producer_v1.spl` (`ab9305d783e`).
3. Production object reuse is **key-based**: module witness match AND `build_cache_entry_is_valid` (own fingerprint + `dep_iface_gate_valid` over the transitive dependency closure of textual `interface_digest_of_source`). `source_interface_parts` (`80.driver/cache/action_key.spl:214`) does not capture `macro ` headers, so a macro contract edit in a dependency leaves `deps_iface` unchanged: **stale object reuse**. The HIR cache key folds every closure member's content hash (`driver_hir_cache.spl:181`) and is therefore never stale (closure-wide conservative, outside this lane).
4. Nothing records what a macro introduces per site (generated items, imports, attributes, AOP-DI effects).

Non-negotiables (plan §8.2, §8.4, §8.6; lifecycle design 2026-10-30):

- Committed complete forward facts (the module `.tld` companion's `macro-def|`, `macro-use|`, `macro-key|` sections) are the only dependency authority. `.rr` accelerates lookup; it never proves "no dependents" on its own.
- Admission is not map presence: a macro facet that is unknown, incomplete, stale, corrupt, or generation-mismatched fails closed (widen with a recorded reason), never "zero dependents".
- A definition's identity never folds in its users (plan 2026-10-24 §6.3). Reference churn never rewrites the provider TLDR.
- Exact means: the invalidated set equals the set of sources whose macro inputs or macro-derived interface changed — no stale reuse, and no unrelated source rebuilt because of a macro edit.

## 2. Shared RR key/edge model (with `generic-rr`)

| Layer | Owner | Macro use of it |
|---|---|---|
| Key | `ReverseReferenceKeyV1` (`00.common/cache/reverse_reference_key.spl`) | projection kinds `macro-definition-consumer`, `macro-name-resolution`, `macro-name-absence` (already registered); `registry_kind = "semantic"`. |
| Edge (semantic) | `ReverseReferenceEdgeV1` over `SemanticQueryKeyV1` (`reverse_reference_shard_v1.spl`) | producer kinds `macro.def` / `macro.resolve`, consumer kind `macro.expand`, produced by `macro_use_forward_read_manifest_v1`; family mapping `reverse_reference_family_for_read_v2`. This is the coordinator / v2 projection path and is unchanged by this lane. |
| Legacy receipt binding | `ReverseReferenceProjectionV1 {key, consumer_identity}` (`reverse_reference_receipt.spl`), consumers are **source paths** | **New in this lane:** root-free subjects `macro-def:<MacroDefId canonical>` and `macro-name:<requested name>`; `projection_digest` = the consumed `MacroDefKey` (definition family) or the candidate root / absence witness (name families). Root-free subjects are required because a changed definition must be looked up by its *old* identity, and name consumers across sites carry different candidate roots. The def key and roots stay the evidence, so the legacy projection and the v2 edge are two bindings of the same forward fact, not two models. |
| Per-file identity facets | `MacroInputRootV1` (own expansion inputs) and macro effect surface (what dependents observe) — new contract `00.common/cache_contract/macro_rr_contract_v1.spl` | both are pure folds over `MacroUseV1` / `MacroDefinitionTableV1`; the generic lane folds its own `ConcreteTldrKey` facet the same way (separate facet, same identity frame). |

## 3. Data flow

```
source edit
  └─ BuildCache.detect_changes (incremental.spl)
       ├─ own fingerprint → Added|Modified|Deleted
       └─ incremental_propagate_dependency_changes
            ├─ receipt read (schema 2 required; generation == BuildCache entries)      [fail closed]
            ├─ per changed path: macro_rr_changed_subjects_for_path_v1
            │     old = raw companion sections (pre-edit), new = re-emitted companion   [fail closed]
            │     → MacroRrChangedSubjectsV1 {definition_subjects, name_subjects}
            ├─ macro_rr_dependents_closure_v1 over inventory def→dependent_macros edges  (macro-uses-macro)
            ├─ receipt consumers per subject/family (exact or widen)
            └─ DependencyChanged for each affected source
build_cache_persist
  └─ incremental_reverse_reference_generation_v2(cache, macro inventory)
       ├─ V1 families as today (source-path facts from the owner snapshot)
       └─ macro families from macro_rr_inventory_v1(entries, tldr_root):
            complete → projections (or explicit known-empty marker); incomplete → @unknown-family
object reuse (driver_aot_native_output)
  └─ witness match AND build_cache_entry_is_valid
       ├─ deps_iface fold: interface_digest_of_source now includes `macro ` headers
       └─ macro facet: recorded DependencyEntry.macro_input_root vs current fold from current definer companions
```

## 4. Module ownership (MDSOC: one authority per concern)

| Module | Layer | Responsibility |
|---|---|---|
| `src/compiler/00.common/cache_contract/macro_rr_contract_v1.spl` (**new, shared**) | common contract | subjects, families, `MacroInputRootV1`, effect surface, `MacroRrDefinitionStateV1`, changed-subject diff, fact derivation, dependents closure. Pure; no I/O. |
| `src/compiler/80.driver/cache/macro_rr_inventory_v1.spl` (**new**) | driver cache | reads companions (`module_artifacts_v1`), decodes macro sections, builds `MacroRrInventoryV1 {complete, reason, modules, facts, all_defs}`; freshness/corruption → incomplete. Re-emits a stale companion through `module_artifacts_emit_v1` when asked (one parse, same as the fiber). |
| `src/compiler/80.driver/cache/macro_rr_invalidation_v1.spl` (**new**) | driver cache | `macro_rr_changed_subjects_for_path_v1`, `macro_rr_affected_sources_v1` (receipt lookup + closure, exact/widen), `macro_rr_current_input_root_v1`. |
| `src/compiler/80.driver/driver_build/incremental.spl` (edit) | driver build | schema-2 generation with macro projections; exact macro propagation replacing the `macro-source-subject-unmapped` widening; `BuildCache.tldr_root`; `DependencyEntry.macro_input_root` recorded and gated. |
| `src/compiler/80.driver/cache/action_key.spl` (edit) | driver cache | `source_interface_parts` captures `macro ` headers. |
| `src/compiler/80.driver/cache/module_artifacts_v1.spl` (edit) | driver cache | `module_tldr_companion_sections_raw_v1(content)` — pre-edit sections without the freshness check (old forward manifest, plan §8.4). |
| `src/compiler/80.driver/cache/reverse_reference_receipt.spl` (no change) | driver cache | schema 2 families already defined; `reverse_reference_consumers_v1` unchanged. |

Not touched: `macro_reference_projector.spl` (forward facts), `reverse_reference_coordinator_v1.spl`, `reverse_reference_projection_v2.spl`, `macro_expansion_cache_v1.spl`, HIR cache key, native witness canonical text, `macro_forward_transport_v1.spl` (advisory file-worker path; it inherits the `macro ` header capture through `driver_native_source_interface_text`).

## 5. Invalidation matrix (what each scenario touches)

| Change | TLDR (companion) of sites | Macro effects record | HIR/MIR/obj of sites | Downstream of sites |
|---|---|---|---|---|
| Macro body edit, same contract | re-emitted (input root changed) | regenerated | invalidated (input root) | **stopped** (site interface + effect surface unchanged) |
| Macro contract/signature edit | re-emitted | regenerated | invalidated (input root; also `macro ` header in deps_iface) | only if site effect surface changed |
| Macro-imported helper edit (helper `fn` in another module) | sites unchanged unless the helper's interface changed (import edge, existing family) | unchanged | body-only helper edit: cutoff at helper's interface (existing contract); signature edit: via `direct-import-export`/deps_iface | existing rules |
| Expansion-site argument edit | site re-emitted (own fingerprint) | regenerated for that site | site only | cutoff unless site interface changed |
| Macro adds/removes a generated symbol | sites re-emitted | changed | invalidated | **propagates**: site effect surface is part of its interface facet |
| Macro renamed / deleted | old-name resolution consumers and new-name absence consumers | regenerated | invalidated | per site interface |
| Transitive macro-uses-macro | dependent definers + their sites (closure) | regenerated | invalidated along the closure | per site interface |
| Unrelated edit | none | none | only the edited file | exact-empty via known-empty family marker; `fallback_reason == ""` |
| Concurrent rebuild | generation mismatch → widen; immutable content + pointer rename, never mixed | — | — | — |
| Corrupt / stale entry | companion stale or corrupt → inventory incomplete → `@unknown-family` → widen; corrupt receipt → invalid → widen; `deps_iface == ""` or unknown macro facet with macro-bearing deps → entry invalid | — | fail closed | — |

## 6. Failure contract

- Receipt missing / undecodable / schema 1 / generation mismatch → widen whole BuildCache scope, reason recorded in `incremental_reverse_reference_fallback_reason_v1`.
- Companion missing / stale / corrupt / wrong section count for any entry → inventory incomplete → macro families `@unknown-family` in the next receipt; lookups answer `exact=false` and widen.
- Changed path whose pre-edit companion cannot be read raw → changed subjects incomplete → widen.
- A consumer source named by the receipt that is not a BuildCache entry → exact=false (receipt/inventory disagreement) → widen.
- `tldr_root == ""` (no companions configured) → macro facet unknown: receipt macro families `@unknown-family`; BuildCache macro gate: entry valid only if no dependency in the closure declares a `macro ` (textual, companion-free); otherwise invalid.
- Deleted files keep the pre-existing whole-scope widening of the legacy caller (all families); a macro removed from a surviving file is a `Modified` edit and is exact.

## 7. Performance envelope

- Inventory build: one companion read per BuildCache entry per `build_cache_persist` (bounded by `macro_reference_max_items_v1`); no repository scan. Changed-path diff: one raw read + one parse (the parse the fiber performs anyway).
- Lookups: linear over receipt projections per subject (same as existing families); closure bounded by the number of definitions in the inventory, visited-set cycle guard.
- Targets to measure once a binary exists: warm incremental no-op on a 200-module fixture with 20 macro sites: zero `DependencyChanged`, `fallback_reason == ""`; macro body edit: exactly the recorded sites rebuilt.

## 8. ADR summary

- **ADR-MRR-1** Root-free subjects in the legacy receipt; full semantic keys in v2/coordinator. Rationale: lookup by old identity; cross-site candidate roots. Alternative rejected: source-path subjects per definer (over-invalidates sibling macros in one module).
- **ADR-MRR-2** Key-based exactness for per-file caches (input root + effect surface), RR used for *which* entries to re-check. Rationale: production reuse is key-based and propagation is dormant; a key cannot be stale, an index can.
- **ADR-MRR-3** Companion = forward authority; inventory is rebuilt from committed companions each generation (plan §8.4), not from the in-process owner snapshot, so unchanged modules keep their edges across incremental builds.
- **ADR-MRR-4** No new `rt_*` leaf calls; publication stays on `reverse_reference_publish_generation_v1` (plan §8.5 CAS/fencing gap remains, documented).
