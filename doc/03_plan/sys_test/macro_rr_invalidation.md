# Macro reverse-reference invalidation test plan

Design: `doc/05_design/compiler/macro_rr_invalidation.md`. Requirements are stated here (no separate requirements doc was requested for this lane); every spec scenario carries one `@req` id below.

| Requirement | Statement | Evidence | Gate |
| --- | --- | --- | --- |
| REQ-MACRO-RR-001 | A macro body edit (same contract) invalidates exactly the recorded expansion sites and the transitive dependent definers; sites' downstream importers are not invalidated. | unit `macro_rr_contract_v1_spec`, integration `macro_rr_invalidation_edit_rebuild_spec`, system `macro_rr_invalidation_spec` | exact set equality |
| REQ-MACRO-RR-002 | A macro-imported helper edit propagates to expansion sites only through the helper's interface facet: a signature edit invalidates sites (deps_iface / `macro ` header capture); a body-only edit stops at the helper. | integration edit-rebuild spec, unit `action_key` macro-header scenario | interface cutoff |
| REQ-MACRO-RR-003 | An expansion-site argument edit rebuilds the site only; no other source is marked changed and `fallback_reason` is empty. | integration | no over-invalidation |
| REQ-MACRO-RR-004 | A macro that adds or removes a generated public symbol changes the site's effect surface, so the site's importers are invalidated; a body-only edit does not change the surface. | unit (effect surface), integration | effect propagation |
| REQ-MACRO-RR-005 | Renaming or deleting a macro invalidates consumers of the old name (resolution family) and consumers that recorded the new name's absence (absence family). | unit (changed subjects), integration | both families |
| REQ-MACRO-RR-006 | A macro-uses-macro chain propagates through `dependent_macros` to the dependent definer and its sites; an unrelated macro in the same definer module is untouched; cycles terminate. | unit (closure), integration | closure exactness |
| REQ-MACRO-RR-007 | An unrelated edit (no macro definitions, interface unchanged) marks only the edited file; macro lookups are exact-empty via the known-empty family marker. | integration, system | no-op reuse |
| REQ-MACRO-RR-008 | Two publishers interleaving generations never expose a mixed receipt; a reader whose expected generation mismatches widens with `stale-generation`. | integration concurrency model | fail closed |
| REQ-MACRO-RR-009 | A corrupt, stale or truncated companion / receipt / cache entry fails closed: inventory incomplete → `@unknown-family` → widen; a cache entry with an unknown macro facet and a macro-bearing dependency is invalid. | unit (inventory), integration, system | fail closed |
| REQ-MACRO-RR-010 | The legacy receipt publishes schema 2 with real macro projections from committed companions; the receipt binds root-free subjects `macro-def:<id>` / `macro-name:<name>` with the def key / root as evidence, and the v2 semantic projection of the same facts yields the same consumer set. | unit (facts), integration (receipt round trip + v2 parity) | one model |

## Specs

| Layer | Path | Scenarios |
| --- | --- | --- |
| unit | `test/01_unit/compiler/cache/macro_rr_contract_v1_spec.spl` | input root (known/complete/empty/conservative/invalid), effect surface stability, changed subjects (body edit, rename, add, remove, incomplete sides), facts for resolved/unresolved/inactive/def-dependency, closure (chain, unrelated sibling, cycle) |
| unit | `test/01_unit/compiler/cache/macro_rr_inventory_v1_spec.spl` | fresh companion, missing, stale, corrupt section, section count ≠ 1, module bound, raw pre-edit read, refresh emits |
| unit | `test/01_unit/compiler/cache/macro_rr_invalidation_v1_spec.spl` | changed subjects for added/modified/deleted; affected sources exact; each widen reason; current input root rewrites (definition-missing, name-now-defined) |
| unit | `test/01_unit/compiler/cache/action_key_macro_header_spec.spl` | `interface_digest_of_source` changes on a macro contract edit and not on a macro body edit |
| integration | `test/02_integration/compiler/cache/macro_rr_invalidation_edit_rebuild_spec.spl` | the nine edit→rebuild scenarios over a real companion fixture tree and a real receipt (REQ-001..009), plus receipt schema-2 round trip and v2 parity (REQ-010) |
| system | `test/03_system/compiler/feature/macro_rr_invalidation_spec.spl` | BuildCache end to end: record entries, publish receipt, edit, `detect_changes`, assert the exact `DependencyChanged` set and `fallback_reason`; no-op; corrupt receipt |

## Commands (self-hosted binary only; a seed run is labelled seed evidence)

```powershell
$RUNTIME = 'bin/release/<triple>/simple'
& $RUNTIME test test/01_unit/compiler/cache/macro_rr_contract_v1_spec.spl --mode=interpreter --coverage
& $RUNTIME test test/01_unit/compiler/cache/macro_rr_inventory_v1_spec.spl --mode=interpreter --coverage
& $RUNTIME test test/01_unit/compiler/cache/macro_rr_invalidation_v1_spec.spl --mode=interpreter --coverage
& $RUNTIME test test/01_unit/compiler/cache/action_key_macro_header_spec.spl --mode=interpreter
& $RUNTIME test test/02_integration/compiler/cache/macro_rr_invalidation_edit_rebuild_spec.spl --mode=interpreter
& $RUNTIME test test/03_system/compiler/feature/macro_rr_invalidation_spec.spl --mode=interpreter
& $RUNTIME spipe-docgen test/03_system/compiler/feature/macro_rr_invalidation_spec.spl --output doc/06_spec --no-index
```

Run each gate once; a failure is fixed in the implementation (max 6 cycles per bug), never by weakening a matcher. Coverage target for `macro_rr_contract_v1`, `macro_rr_inventory_v1`, `macro_rr_invalidation_v1`: > 90 % lines; the number is reported from the runner's coverage summary.

Status 2026-11-01: specs written, UNRUN (no self-hosted binary on this host).
