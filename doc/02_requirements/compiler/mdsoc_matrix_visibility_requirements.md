# MDSOC Feature x Layer Visibility Requirements

Plan: `doc/03_plan/test/language_primitive_mdsoc_visibility_test_plan.md`.

- REQ-MDSOC-MATRIX-001: the numbered layer rule rejects only imports from a higher-numbered layer dir, independent of feature capsule.
- REQ-MDSOC-MATRIX-002: symbol reachability is classified per axis. Layer axis follows the nearest `__init__.spl` boundary; feature axis follows the nearest `dimension = "feature"` capsule (export line, `export use`, or `exports { expose }` port). The two axes may legitimately diverge.
- REQ-LSP-MATRIX-001: `lsp_visibility` reports `layerPublic` / `featurePublic` sets for a requester that agree with REQ-MDSOC-MATRIX-002, and ids that do not depend on the host path style.
- REQ-MDSOC-LAYER-CHECKER-001: the layer checker enforces dependency direction constraints between layers, detects cycles, and manages bypass grants.
- REQ-MDSOC-LAYER-ENFORCEMENT-001: the numbered layer dependency rules are enforced (layer N can only import layers with number <= N).
- REQ-MDSOC-FEATURE-PORTS-001: feature stage port structs can be constructed and their fields are accessible.
- REQ-MDSOC-MEMBER-VIS-001: member visibility enforcement works correctly in HIR lowering.
- REQ-PARSER-FIELD-VIS-001: struct/class field visibility (`pub`, `pub(up)`, `pub(package)`, `pub(friend)`, plain) is carried from the parser to `ParserField.visibility` / `is_public` through the flat decl pool (`decl_field_visibility`, codec `spl-flatpool-v12-field-visibility`); plumbing only, HIR enforcement stays off by default. Spec: test/01_unit/compiler/frontend/flat_pool_field_visibility_spec.spl.
- REQ-LSP-MATRIX-002: lsp_visibility derives the same repo-relative module/feature ids for an absolute (Windows) path as for the repo-relative path.
- REQ-LSP-FORWARD-001: lsp_hover and lsp_definition on a forwarded member (`recv.x` -> field, get_x, is_x, method x; `recv.x = v` -> field, set_x; `recv.m()` via `alias Trait = field` -> the field type's method) resolve to the forwarding target; real fields and explicit outer methods win.
- REQ-LSP-MEMBER-001: lsp_definition on `recv.member` jumps to the member declaration (`file:line: [kind] Owner.name`) of the receiver type for plain fields and methods; `self.x` resolves against the enclosing class/struct/impl; chained receivers `a.b.c` (at most 4 segments) resolve each hop through the field's declared type; unknown types miss cleanly and fall back to the bare-name lookup. Spec: test/01_unit/app/simple_lsp_mcp/lsp_member_definition_spec.spl.
- REQ-LSP-UTF8-001: simple-lsp-mcp JSON scanners and argument/diagnostic parsers use one index unit per scan (char or byte, never mixed), so non-ASCII paths and argument values round-trip exactly and scans stay linear in the char count.
