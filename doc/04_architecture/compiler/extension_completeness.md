# Extension Completeness — Frozen Compiler Contract (Phase 0 lock)

Companion of `doc/02_requirements/language/critical_completeness.md`. Same
rules: one row per frozen item, one embodying file, `UNLANDED` when none.
Lock gate: `sh scripts/check/check-completeness-contract-lock.shs`, hash in
`spec/compiler_schema/contract_lock.sdn`.

## 1. Schema registry format

| Item | Contract | Embodied by |
|---|---|---|
| registry | GENERATED, never hand-edited; `index.sdn` + one `<enum>.sdn` per enum; header `enum_count`/`variant_total` | `spec/compiler_schema/registry/index.sdn` |
| generator | sole writer of the registry | `src/app/compiler_schema/main.spl` |
| freshness gate | regenerate + diff; stale = FAIL | `scripts/check/check-compiler-schema-fresh.shs` |
| visitor generation | derived from registry | `src/app/compiler_schema/visitor_gen.spl` |

## 2. CoverageState (transition tables)

| Item | Contract | Embodied by |
|---|---|---|
| `CoverageState` | `Implemented` / `Normalized(target)` / `Unhandled(reason, issue?)` — no silent arm | `src/compiler/00.common/transition/coverage_state.spl` |
| transition tables | one `.sdn` per producer→consumer boundary | `spec/compiler_schema/transitions/*.sdn` |
| validator | every producer variant has a state | `src/compiler/00.common/transition/validator.spl` |
| gate | 0 missing, n > 0 | `scripts/check/check-compiler-transition-coverage.shs` |

## 3. Extension identity

| Item | Contract | Embodied by |
|---|---|---|
| identity tuple | `owner_enum` + `constructor` + `provider_module` + `local_ordinal` + `payload_schema_hash` + `module_abi_hash` + `schema_abi_version` | `spec/compiler_schema/extensions/hir_async.sdn` (schema by example) |
| dense tag map | stable dynamic tag assignment | `src/compiler/00.common/dynamic_identity/dense_tag_map.spl` |
| manifest parse | `ExtensionManifest`, `ManifestError` | `src/compiler/99.loader/completeness_seal/manifest.spl` |
| required interfaces | `verify, type_check, effects, visit_children, lower_mir, print, hash, serialize` | `src/compiler/99.loader/completeness_seal/required_interfaces.spl` |

## 4. Monomorphization keys

| Item | Contract | Embodied by |
|---|---|---|
| `MonoSemanticKey` | identity of a specialization's MEANING | `src/compiler/40.mono/monomorphize/mono_key.spl` |
| `MonoArtifactKey` | identity of a specialization's ARTIFACT (semantic key + backend/opt axes) | same |

## 5. Aspect / completeness seal schema

| Item | Contract | Embodied by |
|---|---|---|
| seal | a `complete` module seals clean in a critical build once verified | `src/compiler/99.loader/completeness_seal/seal.spl` |
| negative fixture | missing required interface fails the seal | `spec/compiler_schema/extensions/hir_async_missing_serialize.sdn` |
| `dyn` fixture | `dyn` never seals | `spec/compiler_schema/extensions/ide_live_probe_dyn.sdn` |
| aspect seal schema (separate file format) | design §13 | `UNLANDED` |

## 6. Contract lock artifact

`spec/compiler_schema/contract_lock.sdn` holds `contract_hash` = sha256 over
the sorted list of `(path, sha256(content))` for every artifact named in both
docs that is not `UNLANDED`, plus `artifact_count`. Regenerate ONLY with
`check-completeness-contract-lock.shs --update-lock` as a reviewed step.
