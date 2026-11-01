# Detail design: macro reverse-reference invalidation

**Architecture:** `doc/04_architecture/compiler/macro_rr_invalidation.md`. **Test plan:** `doc/03_plan/sys_test/macro_rr_invalidation.md`. **Tasks:** `doc/03_plan/agent_tasks/macro_rr_invalidation.md`.

All names below are frozen for the spec guide; a spec references them exactly.

## 1. Shared contract — `src/compiler/00.common/cache_contract/macro_rr_contract_v1.spl`

Pure functions over the existing `macro_reference_manifest_v1` types. No I/O.

```simple
pub fn macro_rr_family_definition_v1() -> text   # "macro-definition-consumer"
pub fn macro_rr_family_resolution_v1() -> text   # "macro-name-resolution"
pub fn macro_rr_family_absence_v1() -> text      # "macro-name-absence"
pub fn macro_rr_definition_subject_v1(def_id_canonical: text) -> text   # "macro-def:" + id
pub fn macro_rr_name_subject_v1(requested_name: text) -> text           # "macro-name:" + name
pub fn macro_rr_subject_kind_v1(subject: text) -> text   # "definition" | "name" | ""

pub struct MacroInputRootV1:
    known: bool        # every use decodes/validates
    complete: bool     # every use has coverage "complete"
    root: text         # "" unless known and complete
    reason: text       # "ok" | "invalid-use" | "conservative-use"
pub fn macro_input_root_v1(uses: [MacroUseV1]) -> MacroInputRootV1
#   rows sorted by stable_invocation_id, each
#   inv|status-tag|requested name|resolved_def_key or absence_witness|expand_key|generated_symbols_digest
#   root = macro_hash_v1("macro-input-root/v1", rows); zero uses => known-empty root (still a digest).

pub fn macro_effect_surface_v1(def_table: MacroDefinitionTableV1, generated_public_names: [text]) -> text
#   macro_hash_v1("macro-effect-surface/v1", sorted(generated_public_names) ++ sorted(per def: id|exported_surface_digest|public flag))
#   This is the facet a DEPENDENT observes: generated public items plus the exported macro contracts.

pub struct MacroRrDefinitionStateV1:
    def_id: text           # macro_def_id_canonical_v1
    macro_name: text
    key: text              # MacroDefKey (transitive nested root folded)
    dependent_macros: [text]   # canonical ids this definition expands (direct)
    source_path: text

pub struct MacroRrChangedSubjectsV1:
    complete: bool
    reason: text
    definition_subjects: [text]   # macro-def:<id> whose key changed, or present on one side only
    name_subjects: [text]         # macro-name:<name> present on one side only (added / removed / renamed)
pub fn macro_rr_changed_subjects_v1(old: [MacroRrDefinitionStateV1], old_complete: bool,
        new: [MacroRrDefinitionStateV1], new_complete: bool) -> MacroRrChangedSubjectsV1
#   either side incomplete => complete=false, reason "old-forward-incomplete" | "new-forward-incomplete".
#   Body-only edit: definition subject only (name set unchanged) — name consumers are not touched.

pub struct MacroRrFactV1:
    family: text
    subject: text
    consumer: text        # source path
    evidence: text        # def key | candidate root | absence witness
pub fn macro_rr_facts_of_module_v1(source_path: text, defs: [MacroRrDefinitionStateV1],
        uses: [MacroUseV1]) -> [MacroRrFactV1]
#   resolved use   -> (definition, macro-def:<resolved_def_id>, src, resolved_def_key)
#                     (resolution, macro-name:<name>, src, resolution_candidate_root)
#   unresolved use -> (absence,    macro-name:<name>, src, absence_witness)
#                     (resolution, macro-name:<name>, src, resolution_candidate_root)
#   inactive use   -> (resolution, macro-name:<name>, src, resolution_candidate_root)   # guard flip can activate it
#   each def d, each dep in d.dependent_macros -> (definition, macro-def:<dep>, src, d.key)
#   Output sorted and unique by (family, subject, consumer).

pub fn macro_rr_dependents_closure_v1(changed_definition_subjects: [text],
        all_defs: [MacroRrDefinitionStateV1]) -> [text]
#   Worklist over all_defs: a def whose dependent_macros contains a changed id is itself changed.
#   Visited set; bounded by all_defs.len(); result sorted unique; input subjects included.
```

## 2. Driver inventory — `src/compiler/80.driver/cache/macro_rr_inventory_v1.spl`

```simple
pub struct MacroRrModuleStateV1:
    source_path: text
    fresh: bool            # companion exists, source-bound, exactly one macro-def|, macro-use|, macro-key| each, decodes, module ids match
    reason: text
    defs: [MacroRrDefinitionStateV1]
    uses: [MacroUseV1]
    def_table: MacroDefinitionTableV1
    generated_public_names: [text]
    uncacheable_def_ids: [text]   # `macro-key|` flag 1: key kept, every expansion of it conservative
    input_root: MacroInputRootV1
    effect_surface: text
pub fn macro_rr_module_state_v1(source_path: text, tldr_root: text) -> MacroRrModuleStateV1
pub fn macro_rr_module_state_raw_v1(source_path: text, tldr_root: text, recorded_source_hash: text) -> MacroRrModuleStateV1
#   raw = pre-edit sections via module_tldr_companion_sections_raw_v1, admitted ONLY when the companion's
#   source-digest equals `recorded_source_hash` (the BuildCache fingerprint of the pre-edit source);
#   a companion rewritten after the edit is "pre-edit-companion-not-recorded" (fail closed).
pub fn macro_rr_uses_with_uncacheable_v1(uses: [MacroUseV1], uncacheable_def_ids: [text]) -> [MacroUseV1]
pub fn macro_rr_module_state_refresh_v1(source_path: text, tldr_root: text) -> MacroRrModuleStateV1
#   module_artifacts_emit_v1 (no-op when fresh) then macro_rr_module_state_v1.

pub struct MacroRrInventoryV1:
    complete: bool
    reason: text
    modules: [MacroRrModuleStateV1]
    facts: [MacroRrFactV1]
    all_defs: [MacroRrDefinitionStateV1]
pub fn macro_rr_inventory_v1(source_paths: [text], tldr_root: text) -> MacroRrInventoryV1
#   tldr_root == ""  => complete=false, reason "tldr-root-unset"
#   any module not fresh => complete=false, reason "<path>:<module reason>" (facts still collected for diagnostics)
#   > macro_reference_max_items_v1() modules => complete=false "macro-inventory-bound"
```

`generated_public_names` are read from the `macro-key|` section plus `module_public_macro_facts_v1`'s input; if the companion predates the key section it is `fresh=false` ("macro-key-missing").

`module_artifacts_v1.spl` gains `pub fn module_tldr_companion_sections_raw_v1(content: text) -> [text]` (splits sections without comparing the recorded source digest) — the old forward manifest of plan §8.4.

## 3. Driver invalidation — `src/compiler/80.driver/cache/macro_rr_invalidation_v1.spl`

```simple
pub fn macro_rr_changed_subjects_for_path_v1(path: text, kind: text, tldr_root: text,
        recorded_source_hash: text) -> MacroRrChangedSubjectsV1
#   kind "added":    old = [] complete;                          new = refresh(path)
#   kind "modified": old = raw(path, recorded hash) (pre-edit);  new = refresh(path)
#   kind "deleted":  old = raw(path, recorded hash);             new = [] complete
#   Order matters: raw is read BEFORE refresh overwrites the companion. The recorded hash is the
#   BuildCache entry's fingerprint; "" for modified/deleted is "pre-edit-source-hash-missing".

pub struct MacroRrAffectedV1:
    exact: bool
    reason: text
    sources: [text]      # sorted unique source paths; never contains the changed path itself
pub fn macro_rr_affected_sources_v1(receipt: ReverseReferenceReceiptReadV1,
        changed: MacroRrChangedSubjectsV1, inventory: MacroRrInventoryV1,
        known_sources: [text]) -> MacroRrAffectedV1
#   not changed.complete or not inventory.complete => exact=false
#   subjects = macro_rr_dependents_closure_v1(changed.definition_subjects, inventory.all_defs)
#   for s in subjects:        reverse_reference_consumers_v1(receipt, s, definition family)
#   for n in name_subjects:   consumers(n, resolution) and consumers(n, absence)
#   any lookup not exact => exact=false (reason = its fallback_reason)
#   consumer not in known_sources => exact=false "receipt-consumer-unknown:<src>"

pub fn macro_rr_current_input_root_v1(state: MacroRrModuleStateV1, inventory: MacroRrInventoryV1) -> MacroInputRootV1
#   Re-resolves each use's resolved_def_id against inventory.all_defs CURRENT keys; a resolved id that is absent
#   now => known=false "definition-missing"; an unresolved use whose name now has a definition => "name-now-defined".
#   Then macro_input_root_v1 over the rewritten uses.
```

## 4. `incremental.spl` changes

1. `BuildCache` gains `tldr_root: text` (default `""`), set by `build_cache_open_with_tldr_v1(cache_path, tldr_root)`; the AOT driver passes `SIMPLE_FRONTEND_CACHE_DIR` (the same root `driver_parse_shard_entry.spl:244` uses) when set.
2. `DependencyEntry` gains `macro_input_root: text` (persisted as a tagged digest like `interface_digest`; absent in old files reads back `""`).
3. `build_cache_record_entry_with_fp`: when `tldr_root != ""`, `macro_input_root = macro_rr_current_input_root_v1(refresh(source), inventory_of(dependency closure)).root` (`""` when unknown/conservative); `deps_iface` rows become `"{p}={interface_digest_of_source(src)};macro={effect_surface(p)}"` with `effect_surface = ""` when unknown.
4. `build_cache_entry_is_valid`: after the existing gate, the macro gate: if the recorded facet is `""`: valid only if no closure dependency's `source_interface_parts` contains a `macro ` header; else recompute the current input root from current companions and require equality (and the `deps_iface` row equality already covers the effect surface).
5. `incremental_reverse_reference_generation_v1` → emits `schema_version: 2`; iterates `REVERSE_REFERENCE_FAMILIES_V2`; macro families come from `macro_rr_inventory_v1(entries, tldr_root)`: complete → one projection per fact (subject/consumer/evidence as `projection_digest = sha256_text(evidence)`), or the explicit `@known-empty-family` marker when a family has no facts; incomplete → `@unknown-family` with reason digest. `aop-match-membership` and `directory-scope` stay `@unknown-family` (no producer in this lane).
6. `incremental_propagate_dependency_changes`: remove the `schema_version >= 2` widening and the three macro families from `selected_families`; require `schema_version == 2` (schema 1 → widen "receipt-schema-without-macro-families"). For each `Added|Modified` change call `macro_rr_changed_subjects_for_path_v1` + `macro_rr_affected_sources_v1`; exact → add `DependencyChanged`; else widen with the reason. `Deleted` keeps today's whole-scope widening.
7. `interface_digest_of_source` (`action_key.spl`): `source_interface_parts` adds the `macro ` prefix.

## 5. Error handling summary

| Condition | Owner | Result |
|---|---|---|
| companion missing/stale/corrupt/section-count≠1 | inventory | module `fresh=false`, inventory incomplete |
| receipt schema 1 | propagate | widen, reason `receipt-schema-without-macro-families` |
| pre-edit companion's source-digest ≠ recorded fingerprint (rewritten after the edit) | inventory raw | `pre-edit-companion-not-recorded` → changed subjects incomplete → widen |
| `macro-key|` uncacheable flag | inventory | definition key kept; every expansion of it conservative (no input root, site always rebuilt) |
| requested name with > 1 current definition / unresolved name now defined | current input root | `name-ambiguous` / `name-now-defined` → unknown → entry invalid |
| deleted definer | propagate | `deleted` kind: old = raw(recorded hash), new = empty; inventory over the surviving entries (the legacy caller still widens the whole scope for `Deleted`) |
| generation mismatch | propagate (existing) | widen `stale-generation` |
| lookup consumer not a BuildCache entry | invalidation | `exact=false` |
| recorded macro facet `""` and a macro-bearing dependency | entry validity | entry invalid (no reuse) |
| `tldr_root` unset | inventory | `@unknown-family` macro families; lookups widen |
| cycle in `dependent_macros` | closure | visited set; terminates; cyclic defs all reported changed when any member changes (matches `macro-cycle/v1` key marker) |

## 6. Concurrency

Two builders racing on the same `cache_path`: each publishes an immutable content file plus a pointer rename (`reverse_reference_publish_generation_v1`); a reader validates `owner_generation`/`root_generation` against its own BuildCache entries and widens on mismatch. No partial receipt is observable: decode of truncated content is invalid → widen. The companion write is `module_artifact_publish_atomic_v1`. The model spec covers two sequential publishers with interleaved reads; native concurrency qualification is a separate gap.

## 7. Coverage plan (>90 % for touched modules)

Unit specs exercise every branch of `macro_rr_contract_v1` (input root known/complete/empty, surface, diff both sides, facts for the four use states and def dependencies, closure with cycle), `macro_rr_inventory_v1` (fresh, missing, stale, corrupt, wrong count, bound, raw read, refresh) and `macro_rr_invalidation_v1` (added/modified/deleted, exact, each widen reason, current input root rewrites). Coverage is measured with `bin/simple test <spec> --coverage` once a self-hosted binary exists; until then it is UNRUN.
