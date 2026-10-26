# MDSOC Feature x Layer Visibility Requirements

Plan: `doc/03_plan/test/language_primitive_mdsoc_visibility_test_plan.md`.

- REQ-MDSOC-MATRIX-001: the numbered layer rule rejects only imports from a higher-numbered layer dir, independent of feature capsule.
- REQ-MDSOC-MATRIX-002: symbol reachability is classified per axis. Layer axis follows the nearest `__init__.spl` boundary; feature axis follows the nearest `dimension = "feature"` capsule (export line, `export use`, or `exports { expose }` port). The two axes may legitimately diverge.
- REQ-LSP-MATRIX-001: `lsp_visibility` reports `layerPublic` / `featurePublic` sets for a requester that agree with REQ-MDSOC-MATRIX-002, and ids that do not depend on the host path style.
