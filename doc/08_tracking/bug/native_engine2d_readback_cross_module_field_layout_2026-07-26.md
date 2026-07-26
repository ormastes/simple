# Native Engine2DReadback Cross-Module Field Layout

## Status

Source fixed; deployment and live Vulkan readback remain open under TODO 580.

## Evidence

The retained no-stub binary reaches live Vulkan initialization and strict
creation, then segfaults on the first `Engine2DReadback.pixels` access.
Disassembly shows:

- producer allocation: 48 bytes, six fields, `pixels` at offset 0;
- caller projection: tagged pointer correctly untagged, then load at `0x50`.

`resolve_field_index` previously consulted `field_map` through a numeric
`SymbolId` before the lowered local's name-keyed provenance. Symbol IDs are
module-local, so an imported type can collide with an unrelated entry-module
aggregate and return its field index.

## Fix And Check

`resolve_field_index` and `resolve_base_struct_name` now prefer
`struct_value_syms` plus `struct_field_order`, then fall back to HIR IDs.
Resolved and unresolved method calls now share the owner-qualified
`remember_method_return_provenance` helper, so class/struct return identity is
available before field resolution on every dispatch path.

`cross_module_field_layout_source_spec.spl` passes 2/2 with the final
canonical-shape and imported-method fallback assertions.

The Dict/DI collision is now repaired in source. MIR probes the lowered
receiver for nonstatic Dict builtins even when method metadata is positively
but incorrectly resolved, while preserving single evaluation for custom
instance, trait, free-function, and unresolved dispatch. HIR's seven
self-host-sensitive dictionary membership checks call the existing
`rt_dict_contains` owner directly so the first incremental stage can converge.
The focused source contract passes 3/3, and
`native_same_name_has_dispatch_regression_spec.spl` requires a Dict and an
unrelated custom `.has` to both return true.

Three retained-cache driver builds completed without bootstrap or cache reset:
6 compiled/729 cached, 3/732, then 4/731. The resulting driver no longer
segfaults; the original one-file invocation reaches phase 3 and reports only
the expected missing relative import. Supplying both modules parses, lowers,
and analyzes them, but the standalone native driver then logs `no mode
matched, falling through`, exits zero, and writes no binary. Reassigning the
parsed mode after `CliArgs.to_options` and replacing the mode match with direct
enum-discriminant comparisons did not alter that result, proving the
`CompileMode` value is already corrupted before phase dispatch; those
ineffective workarounds were removed.

The three-cycle cap is reached. Resume from the retained cache; do not run a
full bootstrap. Repair and directly regress native `CompileMode` transport,
then compile the existing two-module oracle and expect `84`. Only after that
passes, regenerate the retained Vulkan evidence closure, verify that the caller
loads `pixels` at offset 0, and run one live readback.
