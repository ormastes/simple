# simple_core router depends on stdlib symbols that do not exist

Status: verification-pending (fix lane: work/simple-core-t3, stacked on work/simple-core-t2 via PR base release/1.0.0; PR number to be stamped at merge)

## Symptom
`bin/simple.exe test test/01_unit/app/simple_core/router_spec.spl` -> 1 passed, 2 failed:
`class SimpleCompositionImageV1 has no field named cli_option_route_view`, plus use-warning
`std.nogc_sync_mut.composition.codec` does not provide `admitted_composition_cli_option_route_section_v1`.
`sci_router_section10_contract_spec.spl` fails the same way (pre-existing before #10703).

## Root cause (not a stale spec, not a rename)
`src/app/simple_core/router.spl` (lines 7, 86, 132) and the specs (`router_spec.spl:51`,
`command_resolver_spec.spl:43`, `sci_router_section10_contract_spec.spl:23`) use
`SimpleCompositionImageV1.cli_option_route_view` and
`codec.admitted_composition_cli_option_route_section_v1`, but neither exists anywhere in
`src/lib` on release/1.0.0 or main: `SimpleCompositionImageV1` (composition/types.spl:54) has no
route-view field, `codec.spl` has no route-section function, and there are no
`sci_extension_builder/router` modules. `git log -S` shows the symbol only in the
"rebase(main): transplant current main tree onto release/1.0" commits, i.e. router.spl and specs
landed ahead of the stdlib half (the feature lib was never landed / was dropped in the transplant).
`test/01_unit/lib/composition/sci_extension_router_authored_spec.spl` is marked "intentionally unexecuted".

## Fix needed
Implement the route-view field/type and codec admission function in `src/lib/nogc_sync_mut/composition`
(owner decision: SCI cli_option_route section, see cli_option_route.spl, sci_reader/sci_generator),
or revert router.spl to the shape the stdlib supports. Specs reflect intended behaviour; do not skip/delete.
Until then #10703 equivalence cannot be proven by these specs.

## Fix status (2026-11-23)
Stdlib half implemented: `cli_option_route_view.spl` (view type), codec section-10 encode/decode,
`sci_extension_router.spl`, `sci_extension_builder.spl`. App boundary: `router.spl` collapsed to one
`simple_core_route_v1`, dangling `export` removed from `adapter.spl`. Authored spec reconciled per
Decision 0. Verified: executor, router, sci_router_section10_contract, sci_extension_router_authored,
command_resolver, main specs pass. Still failing and NOT caused by this change:
`provider_dispatch_spec` (`SIMPLE_CORE_PROVIDER_DISPATCH_SKIPPED` undefined in src) and
`provider_abi_digest_admission_spec` (`encode_provider_query_result_v2` undefined in src).
