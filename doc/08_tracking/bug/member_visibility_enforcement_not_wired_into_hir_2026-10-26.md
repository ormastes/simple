# Member visibility policy exists but HIR lowering never enforces it

- Date: 2026-10-26 | Owner area: src/compiler/20.hir/hir_lowering + 00.common/dependency | Size: M
- Symptom: test/01_unit/compiler/hir/member_visibility_enforcement_spec.spl 11/17 fail, all "compile-rejects ..."
  (`expected false to equal true` from `messages_contain(errors, "field \`secret\` is not visible")`,
  "aggregate constructor \`Vault\` is not visible", etc.). The "compile-allows" cases pass trivially.
- Evidence: policy helpers `member_visibility_allows`, `aggregate_constructor_visibility_allows`,
  `member_access_scope_for_modules` (src/compiler/00.common/dependency/member_visibility.spl:71,106,122) are only
  exported (dependency/__init__.spl:74-76) and used by test/01_unit/compiler/dependency/member_visibility_spec.spl.
  No caller in src/compiler/20.hir. No source anywhere emits the diagnostic text "is not visible" for fields
  or aggregate ctors (only a stale comment at 20.hir/hir_lowering/_Expressions/expression_support.spl:241).
  Same on origin/main and origin/release/1.0.0. Field typing (expression_support.spl:225 field_type_for_owner_raw)
  never consults visibility.
- Secondary: peer/up-field tests synthesize sources under `src/compiler/20.hir/...`; log shows
  `[parser_error] ... 1:14: expected Ident, got IntLit '10'` (numbered layer dir `20.hir` lexed as number in a
  generated import path), so layer-path normalization (member_layer_and_tail, member_visibility.spl:47) must not feed
  `20.hir` into source text.
- Repro: `bin/simple.exe test test/01_unit/compiler/hir/member_visibility_enforcement_spec.spl --no-session-daemon`
- Fix: call the policy from field-read lowering and aggregate-constructor lowering, emit the diagnostics the spec expects.
