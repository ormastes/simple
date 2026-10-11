# V3 publication fixture blocked in native monomorphization

## Reproduction

The admitted pure-Simple Stage2 compiler attempted a no-stub LLVM native build of [the focused fixture](../../../test/fixtures/bootstrap_builder/cold_hir_v3_publish_native_main.spl). The fixture constructs a two-source inventory, selects one V3 entry, publishes its real emitted facet files through `cold_hir_package_publish_from_driver_v1`, and checks the persisted CURRENT generation.

The build selected 525 modules. After two HIR passes, the native-build worker reported `[mono] generic_fns=73 call_sites=461 specializations=128 unresolved=33`, then `E-MONO-033`: 33 generic call sites remained unspecialized, so MIR lowering was refused. The worker returned exit code 1. No fixture executable was produced, and no V3 publication PASS is claimed. The bounded 600-second run ended after roughly 9.5 minutes. Evidence: `/tmp/cold-hir-v3-publish-native-build-20261011.log`.

`E-MONO-032` diagnostics identify generic calls to `_sffi_tuple_get` and `_sffi_enum_discriminant` in `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`; `_sffi_enum_payload` and `_sffi_enum_discriminant` in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`; plus `transient_promote`, `array_sort_by`, and tree-sitter outline helpers. These are in the selected compiler closure, outside the new fixture and package-output reader.

## Required repair

Resolve the monomorphization inference failure or reduce the publisher's transitive native closure while preserving the real publication path. Then build and run the fixture with `SIMPLE_NO_STUB_FALLBACK=1`; require V3 CURRENT readback before claiming Item 6 graph publication. A subsequent full CLI warm route and matched p95/RSS cohorts remain separate gates.
