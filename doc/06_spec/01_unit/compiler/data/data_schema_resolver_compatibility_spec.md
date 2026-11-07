# Versioned data schema compatibility

Source: `test/01_unit/compiler/data/data_schema_resolver_compatibility_spec.spl`.
Status: manually authored companion; examples UNEXECUTED. No docgen, maintenance,
runtime compatibility or production verification PASS is claimed.

The examples retain a known V1 serialization digest, canonical attribute/alias
results, declaration-provenance ordering and schema-local ordinal assignment.
Invalid declaration/owner diagnostics preserve input order before reduction.
Type conflicts preserve the exact established message and take precedence over
requiredness conflicts for the same duplicate declaration. V2 retains explicit
fieldless views, properties, contract version and its frozen V1 projection.

These expectations protect the internal reducer/property/SDN extraction while
the public V1/V2 wrappers remain available. The unchanged original V1/V2 unit
specifications are also required when an admitted runtime is available. Static
digest-body equality is useful source evidence but does not replace executing
these cases and the existing specifications.
