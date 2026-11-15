# Seed parser rejects a field-level `@attr_storage(...)` in a class/struct

Status: verification-pending (parser fix + cargo test authored; not in a deployed seed)
Found by: lane nodeattr seed-acceptance spec
`test/02_integration/compiler/data/node_attr_seed_acceptance_spec.spl`

Seed-tip: `Unexpected token: expected Fn, found Identifier { name: "inferred" }` for
`@attr_storage("sparse_hash")` on its own line before a class field. Class-level
`@attr_storage` parsed already. The class-body gate treated every `@` as a method
decorator except `@collection_algorithm`; `parse_field` rejected every other attribute.

Fix: `is_at_field_annotation()` (parser_impl/attributes.rs) + `parse_field` accepts and
ignores `attr_storage` (seed does not implement storage; pure-Simple compiler does).
Cargo test: `parser/tests/attr_storage_field_annotation.rs`.
The Simple spec stays RED on the stale seed-tip binary until a seed carrying this fix is deployed.
