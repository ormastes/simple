# V3 publication native monomorphization repair and MIR timeout

## Reproduction

The admitted pure-Simple Stage2 compiler attempted a no-stub LLVM native build of [the focused fixture](../../../test/fixtures/bootstrap_builder/cold_hir_v3_publish_native_main.spl). The fixture constructs a two-source inventory, selects one V3 entry, publishes its real emitted facet files through `cold_hir_package_publish_from_driver_v1`, and checks the persisted CURRENT generation.

The build selected 525 modules. After two HIR passes, the native-build worker reported `[mono] generic_fns=73 call_sites=461 specializations=128 unresolved=33`, then `E-MONO-033`: 33 generic call sites remained unspecialized, so MIR lowering was refused. The worker returned exit code 1. No fixture executable was produced, and no V3 publication PASS is claimed. The bounded 600-second run ended after roughly 9.5 minutes. Evidence: `/tmp/cold-hir-v3-publish-native-build-20261011.log`.

`E-MONO-032` diagnostics identify generic calls to `_sffi_tuple_get` and `_sffi_enum_discriminant` in `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`; `_sffi_enum_payload` and `_sffi_enum_discriminant` in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`; plus `transient_promote`, `array_sort_by`, and tree-sitter outline helpers. These are in the selected compiler closure, outside the new fixture and package-output reader.

## Required repair

Resolve the monomorphization inference failure or reduce the publisher's transitive native closure while preserving the real publication path. Then build and run the fixture with `SIMPLE_NO_STUB_FALLBACK=1`; require V3 CURRENT readback before claiming Item 6 graph publication. A subsequent full CLI warm route and matched p95/RSS cohorts remain separate gates.

## Bounded repair result

A grouped source repair added explicit type arguments at the failing SFFI,
promotion, and recursive sort call sites; made the outline's ignored handler
type concrete; and gave the LLVM MIR instruction discriminant helper a local
unique name. The second no-stub Stage2 LLVM attempt reduced unresolved
generic calls from 33 to 2. Its remaining diagnostics were the LLVM helper
name collision and the `identity` promotion call on a shared source line.

The third and final bounded attempt used both corrections. It reported
`[mono] generic_fns=71 call_sites=438 specializations=134 unresolved=0`
and entered `phase=mir` with 525 modules. The 600-second limit ended before
the first MIR module completed; no executable was produced. Evidence:
`build/mini_builds/target6_v3_mono_cycle2.log` and
`build/mini_builds/target6_v3_mono_cycle3.log` in the isolated worktree.
The three-cycle verification cap is reached for this fixture in this session.

The E-MONO-033 blocker is resolved for this exact source closure. The
remaining gate is a bounded build that reaches MIR, native link, fixture
execution, and V3 CURRENT readback. Preserve the frozen source revision and
cache lineage for that follow-up; do not infer a publication PASS from
`unresolved=0`.
