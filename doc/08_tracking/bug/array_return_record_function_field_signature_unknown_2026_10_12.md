# Array return records with function fields lacked a complete semantic snapshot

Status: source repair implemented; native validation pending. No compilation or execution pass is claimed.

The provider semantic field-signature helper `result_err_field_type_key` previously had no Function arm. This made a complete record snapshot unavailable even though the independent function-field ownership registry could encode the field. The conservative array-record guard therefore would have rejected valid returned record arrays.

Actual compiler consumers include `compiler/90.tools/aop.spl` functions `advices_for` and `sort_advices_by_order`, returning `[Advice]` with `handler: fn(text, [Value]) -> Value`; and `compiler/90.tools/lint/static_rules.spl` function `static_lint_rule_table`, returning `[StaticLintRule]` with `check_fn: fn(LintParamsV1, LintUnit) -> [StaticLintFinding]`. The MCP-owned tool descriptor records have no direct function-valued fields.

The snapshot now recursively encodes Function parameters, return type, and effects. Nested nominal types use canonical identities resolved in the defining table. Explicit Any remains a known type; Infer, Error, TypeParam, missing nominal declarations, and unsupported shapes reject the snapshot. Throws effects recursively encode their type and participate in the separate function-field ownership/rebinding traversal, so their Named IDs cannot remain provider-local. No callable body or provider SymbolTable is retained.

The positive fixture is `test/fixtures/compiler/native_array_return_function_field_owner/main.spl`. It retains actual prefix and callback assertions, nominal parameter/return ownership contested by consumer homonyms, iteration and indexing, and an explicitly Any-typed callback field. The former rejection fixture was converted to this positive contract rather than treating valid Function fields as permanently unsupported. It has not been native-built or executed.

A valid zero-field record has the complete snapshot `fields[]`, not an empty string. `native_array_return_record_owner` keeps a positive zero-field record array iteration regression so missing metadata cannot be conflated with an empty declaration.
