# XRay V1 integration status — 2026-11-03

Status: implementation in progress; not backend qualification or release admission.

The full user-supplied [staged design](simple_xray_staged_implementation_plan_2026-11-03.md) is retained with line-end whitespace normalized. Its historical external evidence is user-supplied; this integration has not independently rerun those workflows or merged draft PR #5962.

## Superseding decisions

- Use a backend-neutral Simple facade across Linux LLVM, Linux Simple-owned, then Windows Simple-owned implementations.
- Retain tracing code, maps, descriptors and providers until process exit. Logical release never means hot unload. Existing general-purpose dynload behavior is unchanged.
- One process capture session; raw edges are baseline. Exact spans and live patching require separate admitted capabilities. Raw folder depth becomes unknown after gaps until resynchronization.
- Windows tracing stays off through stages 1–2. Linux dependencies must be excluded before Windows build evaluation. SimpleOS XRay-OFF remains intact.
- Observer hooks collect bounded records; deferred consumers run aspect behavior. No arbitrary plugin callback in a hidden machine hook.
- Instrumented-but-disabled and statically-off are distinct products. Earlier development-default tracing remains gated on the new target/profile qualification and PERF-01; it is not automatically enabled by this interface patch.

## Current slice

The separate, unlanded interface draft `common.trace.observer_contract_v1` declares the language-level provider port, typed configuration/capabilities, statuses, generation-bearing handle values and canonical event tags. `AspectParamsV1` gains only the named extension constant; its fields, ordinals and defaults are unchanged. No backend or OS dependency is imported and no capability is advertised as implemented.

The proposed 96-byte little-endian event format has an 8-byte header (u16 schema=1, u16 size=96, u16 kind, u16 flags), generation at 8, module instance at 16, u32 function/site at 24/28, context/sequence/timestamp/span at 32/40/48/56, three u64 kind-specific payload slots at 64/72/80 and reserved zero at 88. This is an explicit wire proposal, never the Simple struct layout. Typed allocation/access events remain unsupported; adding their semantics needs explicit capability admission.

W0 is NOT complete: the event/config codecs, generated native ABI caller-buffer validation, golden byte fixtures and actual admitted-runtime compatibility execution remain required. The interface spec is authored, UNRUN. The trait deliberately has no fake backend implementation. Numeric handles are untrusted lookup keys; only a provider-issued resident table entry grants authority.

## PR2 `xray-v1-contract` (2026-11-06)

Re-rooted on `release/1.0.0` (not merged/rebased from the draft branch): `src/lib/common/trace/observer_{contract,config,event_codec,session,collector,native_map,native_abi,build_route,aspect_config}_v1.spl`, `src/lib/nogc_sync_mut/trace/observer_native_channel_v1.spl` (producer release uses the seed+C backed `rt_par_atomic_add_i64(-1)`), and the `simple.trace/observer-v1` constant in `aspect_params.spl`. The 9 draft lib specs now RUN green on the Rust seed (65 examples; the session reference model is a caller-owned value, no module globals). Compile-time intake is ONE gate, `xray_observer_request_check` in `80.driver/driver_xray_policy.spl`, decided once in `CompileContext.create` and stored as `xray_config_error` (the five draft entry-point calls and the `weave_aop` call are gone). It only rejects; it never changes `xray_mode`. Not ported: the `has_errors` early return (Q9, own PR), `observer_llvm_adapter_v1` + hosted-linux fixture (PR4), `mir_observer_site_intent_v1` (superseded), `observer_llvm_host_shim_v1` (PR3).

## PR3 `xray-llvm-attrs` (2026-11-06)

`MirFunction.xray_mode` now reaches LLVM IR as `"function-instrument"="xray-always"` (never-list: `xray-never`, only in instrumented modules; no threshold). `trace.instrumentation` SDN key and the `xray-v1` CompileOptionsHash component (LiveKey pos 49) landed with it. Not yet: `clang_rt.xray` link and the handler shim (PR4), so a `--xray` LLVM binary carries unpatched sleds only.

## Ordered remaining work

1. W0: implement/review codecs, native ABI and golden fixtures; validate with admitted self-hosted tooling; then freeze the contract.
2. W1: bounded collector and generation admission/drain with model-linked native race tests.
3. W2/W3: pinned Linux LLVM shim and real Simple-generated ABI tests; prove Windows-off isolation.
4. W4/W5: Simple-owned emitter/maps/POSIX patch leaves, native Linux qualification and adapter differential tests.
5. W6: independently qualify Windows x64 and ARM64 profiles, including per-binary protection policy association.
6. W7: incrementally admit wider ISA/LTO/live-patch/exact-span modes, never silently fall back.

The earlier visibility/AOP, LSP/MCP, profile and cache/RR requirements remain independent unfinished work. Source-only patches are not passes. Compiler bootstrap Phase 3 is distinct from Windows XRay stage 3.

## Bootstrap coordination

Attempt 7 built Phase 2 and passed its executable sanity but the full verification was stopped by the 20-GiB disk floor. Its outer receipt confirms quiescence; no Phase 3 pass is claimed. The fix-rr branch was rebased to current release with conflict reconciliation; source-dependent checks must use the new source identity. Fetch uses an explicit release refspec because this checkout's configured fetch only tracks release_phase3.
