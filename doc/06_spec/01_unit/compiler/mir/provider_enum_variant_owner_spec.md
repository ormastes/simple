# Compact enum provider variant owners

Source: `test/01_unit/compiler/mir/provider_enum_variant_owner_spec.spl`.
Status: authored, **UNEXECUTED**.

Register a real body-free enum declaration and provider symbol table through
`register_provider_enum_from_declarations_v1`. Require both its qualified
variant table and inverse constructor-owner table. Re-registration remains
unique; a distinct enum sharing the variant spelling produces two owners.

This tests the actual registration owner rather than matching source text.
It does not execute native constructor recovery or attribute a bootstrap
failure to the duplicate definition.
