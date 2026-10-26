# Language Primitive and MDSOC Visibility Test Plan

Status: draft 2026-10-26. Scope: language primitives, visibility, accessor forwarding, and the
MDSOC feature x layer matrix. Lanes: interpreter (default) and `SIMPLE_JIT_STRICT=1`.

References: `doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md:123-129,279-296`,
`doc/05_design/app/mcp/mdsoc_visibility_requester_design.md:32-78`,
`src/compiler/85.mdsoc/layer_checker.spl:562-590`,
`src/compiler/00.common/dependency/member_visibility.spl:106-120`,
`src/compiler/35.semantics/visibility_checker.spl:155-242` (W0401-W0405).

## 1. Primitive matrix

Every row runs on both lanes (interp, `SIMPLE_JIT_STRICT=1`); a lane divergence is a bug record, not a skip.
Spec paths are under `test/01_unit/`.

| Area | Existing spec | Gap |
|------|---------------|-----|
| Bindings (`val`, `var`, shadowing, `if val`) | `language/if_val_binding_shadows_module_global_spec` | `.?` yields `T?` (use `.is_some()` for bool); no strict-lane twin |
| Primitive types, receiver methods | `language/primitive_receiver_trait_impl_dispatch_spec` | f64/u8 width edges |
| Traits / impl dispatch | same spec | trait on generic receiver |
| Generics `<>` | `compiler/50.mir/generic_struct_composite_field_spec` | generic fn over enum payload |
| Enums / match | `language/enum_match_dispatch_spec` | nested payload exhaustiveness |
| Option / Result | `dict_get_option_match_spec`, `result_unwrap_payload_type_preserved_spec` | `.?` into `val` (see row 1) |
| Closures | `closure_capture_write_spec` | capture of `var` across JIT boundary |
| Modules / use / export | `compiler/20.hir/export_origin_generated_comment_foreign_package_spec` | re-export chain of 3 hops |
| Visibility pub / private / file / capsule | `compiler/dependency/member_visibility_spec`, `compiler/visibility_spec` (parse error, "filenames" token; the `compiler/dependency/visibility_spec` twin is a different, passing file) | file-level `pri` vs capsule; fix parse error |
| Field forwarding `alias Trait = field` | `language/accessor_forwarding/` (seed only) | self-hosted `20.hir/hir_forward_lowering.spl:28-29` lowers only `alias fn/me NAME = FIELD.METHOD`; trait alias forms unsupported |
| Getter/setter forwarding `get_/is_/set_` | `language/accessor_forwarding/` | self-hosted has none; `+=` through a forwarded setter is unsupported (assert diagnostic, do not silently allow) |
| Interp vs `SIMPLE_JIT_STRICT=1` | `lsp_visibility_support_spec` runs interp only | per-row twin via strict lane |
| MDSOC feature x layer | none end to end before this plan | `compiler/mdsoc/feature_layer_matrix_spec`, `app/lsp/lsp_feature_layer_matrix_spec` |

Legacy (no `step`/`@req`) specs to modernize: most of `compiler/mdsoc/*`, `hir/member_visibility_enforcement_spec`.
Currently red on seed (sha 9544a61d7824 = `C:/dev/simple/bin/simple.exe`; re-measure before relying): `mcp_visibility_requester` 2/6, `native_capsule_result_receipt` 7/8, `module_loader_runtime_capsule` 0/1.

## 2. MDSOC 2-D matrix

Fixture: `test/fixtures/mdsoc_matrix/` with features A, B; layers lower `10.core`, higher `20.app`;
cells a10, a20, b10, b20. Each cell has `api` (pub, exported in capsule `__init__.spl`),
`inner` (pub, not exported), `secret` (no pub).

### 2.1 Layer axis (numbered rule, `check_numbered_layer_dep`)

Layer N may import layers <= N. Feature is not consulted.

| from \ to | a10 | a20 | b10 | b20 |
|-----------|-----|-----|-----|-----|
| a10 | ok | VIOLATION | ok | VIOLATION |
| a20 | ok | ok | ok | ok |
| b10 | ok | VIOLATION | ok | VIOLATION |
| b20 | ok | ok | ok | ok |

Violation message: `layer 10 (10.core) cannot import from layer 20 (20.app)`.

### 2.2 Symbol visibility, every ordered requester -> owner pair

Expected `lsp_visibility` / `visibility_json` fields (owner O, requester R; "same" = R's feature equals O's feature):

| Symbol | display | simpleVisibility.reachable | featureVisibility.exported | featureVisibility.reachable | layerPublic | featurePublic (why) |
|--------|---------|----------------------------|----------------------------|-----------------------------|-------------|---------------------|
| api | public | true for all 16 pairs | true | true for all 16 | listed, all pairs | listed, "named in an export line of a capsule __init__.spl" |
| inner | boundary | true iff same feature (or same file) | false | true iff same | listed iff same | listed iff same, "same feature capsule as requester" |
| secret | private | true only if R file = O file | false | true iff same | never | not listed unless exported (private is skipped for requester sets) |

Cell-pair summary (rows requester, columns owner; E = exported only, E+F = exported plus feature-internal):

| R \ O | a10 | a20 | b10 | b20 |
|-------|-----|-----|-----|-----|
| a10 | all | E+F | E | E |
| a20 | E+F | all | E | E |
| b10 | E | E | all | E+F |
| b20 | E | E | E+F | all |

Verdict composition: an import is legal only if the layer rule passes AND the symbol is reachable.
a20 -> b10: layer ok; api reachable, inner and secret not. a10 -> a20 api: symbol reachable but import still a layer violation.

### 2.3 Spec ambiguities (docs silent; specs assert current behavior and flag it)

1. The tobe doc has no upward-import rule across features; only the numbered rule rejects 10 -> 20, regardless of feature.
2. `imports { deny }` is documented as NOT enforced (design doc 63-66); no spec may expect a deny verdict.
3. Feature axis ignores the `pub` keyword: a `secret` is feature-reachable from a sibling layer of the same capsule while layer-unreachable. Intended or not is undecided.
4. `query_visibility` does not apply the numbered layer rule to reachability; layer and import checks are separate verdicts.
5. Same-layer cross-feature import (a20 -> b20) is layer-legal; whether features may depend on each other at all is only governed by exports.

### 2.4 Member visibility (checker policy)

`member_visibility_allows`: public always; private same_module; package same_package (feature id used as package);
internal same_package or declared friend with internal export; up same_module or immediate parent facade; peer same_module or peer logical path.
Warnings W0401-W0405 must be exercised by a compile-level spec once `visibility_spec` parses.

## 3. Execution

`timeout 600 bin/simple test <spec> --no-session-daemon`; record executed/passed/failed per spec. Reds that expose product bugs stay red with a bug record.

## 4. Review follow-ups (2026-10-26)

1. Nested boundary: `feature_a/10.core/__init__.spl` (exports only `a_core_inner`) separates the axes for cell a10.
   Layer axis reads the NEAREST manifest (`exported_by`, `query_commands.spl`); feature axis reads EVERY manifest up to the capsule root
   (`feature_manifest_exports`). Result: `a_core_api` is layer `boundary` (unreachable by outsiders) yet feature-exported; `a_core_inner` is public on both axes.
   Ambiguity: a nested layer export implies feature export; unconfirmed as intended.
2. Gap: `layer_checker.spl` has no file-level checker (only `check_layer_dep` and `check_numbered_layer_dep`, both taking directory strings).
   The layer steps of the specs therefore feed 4 distinct dir-name inputs, not fixture imports. A fixture-import layer check is unwritten.
3. LSP spec cost: each `lsp_visibility` call spawns the deployed binary (needs `bin/simple.exe` on Windows, ignores `SIMPLE_JIT_STRICT`, so no strict-lane twin).
   The 16 pairs are fetched once and cached; the no-requester view adds 4 calls.
4. Extra cases covered: no-requester view, `export use m.{A}`, `exports { expose }` port (open vs hidden), secret absent from `featurePublic`, `same feature capsule as requester` why.
5. Member policy uses `package_name(path)`; fixtures sit outside `src/`, so every cell has package `test` and the Package kind is trivially allowed. Internal/Up/Peer and W0401-W0405 remain uncovered.
6. Windows defect: absolute paths yield ids like `C:.dev.wt-mdsoc.test...`; see `doc/08_tracking/bug/lsp_visibility_windows_abs_path_module_id_2026-10-26.md`.
7. `.?` is `T?` pass-through per the syntax quick reference (`val x = f().?` binds the Option); use `.is_some()` for a bool. Not a bug; the earlier suspicion is withdrawn. Row 1 of section 1 should read "`.?` yields T?, not bool".
8. Requirements registered in `doc/02_requirements/compiler/mdsoc_matrix_visibility_requirements.md`.
