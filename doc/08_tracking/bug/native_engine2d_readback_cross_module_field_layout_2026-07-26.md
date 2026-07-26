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
`cross_module_field_layout_source_spec.spl` passes 1/1.

The bounded incremental rebuild reached its three-cycle cap without a usable
CLI. Resume from the existing cache; do not run a full bootstrap. After
deployment, regenerate the retained evidence closure and verify that the caller
loads `pixels` at offset 0 before one live Vulkan readback run.
