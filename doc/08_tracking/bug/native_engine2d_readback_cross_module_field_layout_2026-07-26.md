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

The third bounded incremental build reused 732 objects, compiled three, and
linked `build/gpu-goal/source-matched/simple.driver.stubbed`. Its `--help`
smoke passes, but compiling the two-module native regression segfaults after
argument parsing. GDB resolves the crash to `DiContainer.has`, called from
`HirLowering.lower_hir_expr`; typed-map `.has(...)` calls in that function were
misbound to the unrelated DI method in the native compiler capsule. The
release-runner system spec also timed out after selecting the forbidden Rust
seed path, so neither result is native acceptance evidence.

The three-cycle cap is reached. Resume from the retained cache; do not run a
full bootstrap. First repair and directly regress native method selection for
same-named `.has` methods, then compile the existing two-module oracle and
expect `84`. Only after that passes, regenerate the retained Vulkan evidence
closure, verify that the caller loads `pixels` at offset 0, and run one live
readback.
