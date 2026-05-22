<!-- codex-design -->
# Security Convention-First Architecture Detail Design

## Data Flow

1. `infer_security_coordinate(path)` extracts `layer`, `feature`, `trust`, `runtime`, and `security_root`.
2. `build_feature_graph` extracts source-level imports and call-like references.
3. `build_hir_feature_graph` extracts resolved HIR imports and referenced symbols when modules are available.
4. `source_security_violations_sdn_with_modules` emits diagnostics.

## Coordinate Inference

For `src/<layer>/<feature...>/<file>.spl`, the first segment after `src` is accepted when it is one of the built-in layers. The feature is the remaining directory path, excluding the file name, joined with dots.

Example:

`src/service/user/profile/profile_service.spl` -> `layer=service`, `feature=user.profile`.

## SEC101

`SEC101` is emitted only for same-feature edges with both source and target layers known.

The initial rule is conservative:

- `to_layer_index > from_layer_index + 1` is a skip.
- Same layer and adjacent layer are not reported by this diagnostic.

## Tests

Compiler tests cover:

- Convention-first coordinate inference.
- `ui -> domain` same-feature import reports `SEC101`.
- `service -> domain` same-feature import does not report `SEC101` or `SEC201`.
