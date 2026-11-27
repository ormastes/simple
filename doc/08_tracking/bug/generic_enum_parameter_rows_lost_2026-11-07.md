# Enum generic parameter bounds and defaults are discarded

Status: parser transport repair and regression specifications authored;
runtime verification pending.

`parse_enum_decl` used `parse_type_params`, which returns only parameter
names. The canonical helper also parsed supported inline bounds and default
types, but the enum declaration never stored those rows. The flat-AST bridge
then rebuilt every enum parameter with empty bounds and `has_default: false`.
Thus `enum Message<T = text>` could reach the parser module with the name `T`
but without its declared default.

The repair uses `parse_type_params_with_trait_bounds` and the existing
`decl_set_type_param_constraints` row storage. Enum bridge conversion reuses
`convert_decl_function_type_params`, as the function/class/alias paths do.
The existing enum span sentinel is captured before bound/default fragments
are reparsed. No generated fields or codec layout changes are introduced:
the current flat-pool codec already writes/restores parameter names and rows,
and canonical frontend-cache identity includes the compiler source fingerprint.

This change transports parser metadata. Applying omitted nominal arguments,
validating arity, and resolving default declaration ownership remain with the
HIR nominal type owner. Synthetic enum implementation parameter-bound
inheritance is not changed. Parameterized inline trait bounds remain the
separate inherited grammar limitation recorded by the generic-alias report;
this fix uses the existing supported bounds and default syntax.

`test/01_unit/compiler/frontend/generic_enum_parameter_transport_spec.spl`
parses actual enum source with bare/conjunctive bounds, scalar and dependent
array defaults, and named generic payloads. It covers required/non-generic
controls, actual flat-pool restore after unrelated state reuse, existing class
and function default paths, and a missing-default parser rejection.

`test/fixtures/compiler/generic_enum_parameter_transport/main.spl` is a
standalone payload-value control with explicit enum arguments and a declared
default. It deliberately does not qualify omitted-argument HIR behavior.

The isolated starting release is
`5709105f40e6814a4cbd75c268436e6c64351043`. Shared source files contain edits
only in enum parameter capture/storage and enum parameter bridge conversion,
plus the shared setter import. Alias and node-tree attribute regions must be
preserved during latest-release integration.
The landed alias changes from PR #7581 are preserved in the integrated source
owners used for the enum candidate.

No admitted self-hosted compiler test, native compile, or executable was run;
no Rust seed was used. Source review and authored specifications are not an
executed PASS. Resume the focused frontend spec and native payload fixture
through an admitted self-hosted runtime, then required compiler/core and
MCP/LSP checks. Nominal default application requires its owner's independent
verification.
