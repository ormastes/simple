# TLDR: Language Primitive and MDSOC Visibility Test Plan

Full plan: `doc/03_plan/test/language_primitive_mdsoc_visibility_test_plan.md`

- Goal: one matrix covering primitives, visibility, accessor forwarding, and feature x layer MDSOC rules.
- Lanes: interpreter and `SIMPLE_JIT_STRICT=1`; divergence is a bug record, never a skip.
- MDSOC fixture: `test/fixtures/mdsoc_matrix/` (features A,B x layers 10.core, 20.app = 4 cells).
- Symbols per cell: `api` (exported), `inner` (pub, unexported), `secret` (private).
- Layer rule: only 10 -> 20 imports are violations; feature is not consulted.
- Feature rule: exported symbols reachable everywhere, others only inside the same capsule.
- Specs: `compiler/mdsoc/feature_layer_matrix_spec`, `app/lsp/lsp_feature_layer_matrix_spec`.
- Known gaps: self-hosted lacks `get_/is_/set_` and `alias Trait = field` forwarding; `+=` via setter unsupported.
- Ambiguities: no upward rule across features; `imports deny` unenforced; feature axis ignores `pub`.

```sdn
matrix:
  features: [A, B]
  layers: [10.core, 20.app]
  cells: [a10, a20, b10, b20]
  layer_violations: [a10->a20, a10->b20, b10->a20, b10->b20]
  reachable:
    api: all
    inner: same_feature
    secret: same_file_layer, same_feature_axis
```
