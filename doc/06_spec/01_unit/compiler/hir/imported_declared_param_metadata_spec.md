# Imported declared parameter metadata

Executable: `test/01_unit/compiler/hir/imported_declared_param_metadata_spec.spl`.
Status: authored, UNRUN with the changed compiler. Codec generation alone passed.

1. Parse a provider method without a return annotation accepting text, an imported
   nominal enum and f64. Import only its class into a consumer with a same-named
   decoy type. Assert exact owner-qualified enum identity, four declared parameters,
   unchanged absent return type, and the actual MIR callee's f64 ABI parameter.
2. Encode and decode the actual HIR module with the generated codec, repeating
   owner/ABI assertions after transport.
3. Distinguish a known empty declaration from an unannotated parameter declaration.
4. Rename the callable while preserving independent declaration metadata and
   leaving its return-type inference state unchanged.

Public tracing, bootstrap admission, inferred return types and instantiated generic
callable ABI qualification are not established by these scenarios.
