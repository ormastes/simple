# Bootstrap module-static export visibility

Source: `test/01_unit/compiler/hir/bootstrap_export_static_visibility_spec.spl`.
Status: AUTHORED / NOT_RUN; docgen and native linkage are not qualified.

1. **Prepare the real fixture.** Parse an exported private mutable static, an unexported private mutable static, an exported immutable literal, and an explicitly package-visible exported static. Save the two ambient bootstrap variables.
2. **Invoke the production owner.** Four scenarios call `lower_parser_module_unstub` and direct `lower_module`, each in bootstrap and normal modes. Observe `ambient_bootstrap_enabled` before lowering. `SIMPLE_BOOTSTRAP_STAGE4=1` isolates wrapper constant recovery from the unrelated flat-pool projection; it does not disable the direct owner's bootstrap branch. Restore both variables before assertions.
3. **Check the observed contract.** Require all four named constants and no lowering errors. Only the exported private mutable static becomes Public with `is_public=true`; the unexported mutable and immutable literal remain Private, and explicit Package visibility survives. Check mutability as well as visibility.

These controls exercise the real parser and both bootstrap lowering paths, not a copied visibility helper. They do not establish native accessor linkage or T32 execution. Existing normal lowering tests and PR #7300's separate declaration-level workaround remain distinct evidence. No prior native success transfers to this new source revision.
