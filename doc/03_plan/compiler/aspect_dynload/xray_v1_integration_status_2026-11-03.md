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

W0 is NOT complete. Cold-path event and strict SDN configuration codecs and golden/malformed-record fixtures are authored but UNRUN. Configuration has an exact schema descriptor/SHA-256, conservative off defaults, explicit profile requirements, duplicate/unknown-key rejection and resource bounds. The event tests include full-field and bit-63 goldens. Generated native ABI caller-buffer validation and actual admitted-runtime compatibility execution remain required. The event codec performs structural decoding only; it does not certify generation authority, paired-span validity or complete coverage. The trait deliberately has no fake backend implementation. Numeric handles are untrusted lookup keys; only a provider-issued resident table entry grants authority.

The named AspectParams extension now has bounded strict UTF-8/schema intake at `weave_aop_with_params`, including duplicate-extension rejection. Absent or explicitly off configuration preserves the ordinary AOP path. Active Windows/foreign targets reject; canonical Linux routes identify candidates only and the driver rejects them as `UnsupportedProfile` until actual admission exists. This wiring does not establish coverage of every compiler entry point or a native dependency-graph comparison.

Additional source-only slices are authored: W1 serial reference collector/session core; W2 cold LLVM callback-map translation; W3 early off/candidate routing; W4 structural native maps, checked branch/template construction and MIR site-intent planning. W1 requires external serial ownership and does not implement the provider trait or native atomic admission. W2 imports no runtime and provides no callback shim/profile. W4 does not insert machine sleds, decode/register a loaded image or authorize patching. All new specs remain UNRUN; no native or production readiness is claimed.

The old uncomposed linked-startup packets still retain both accepted P1 findings: writable overlapping PT_LOAD aliases and stale activation-policy checks after external work. Rejecting overlaps in the new structural map owner is not a repair of those packets. Their retained sources and hashes must not be imported without both fixes and renewed review.

## Native-boundary continuation

The second source tranche adds a draft copied-buffer request/response owner (144-byte request, 64-byte response), strict config-schema/selection metadata, operation-specific lengths and reserved-field checks, and explicit copied output. It does not export a native entrypoint, dereference caller pointers, or establish handle issuance. Native buffer leasing and provider dispatch remain open.

Compiler request rejection is now propagated at actual compile, VHDL, JIT, AOT and object-emission entry points; JIT/AOT stop after weaving errors. The earlier weave-only guard could accumulate an error and still reach execution/codegen. New owner-entry specs cover that source correction but are UNRUN.

An optional Linux x86-64 LLVM23 effectful candidate is staged as `test/fixtures/trace/hosted_linux/observer_llvm_linux_v1.spl`, outside default source roots. It initializes LLVM, installs a resident handler, validates object/function IDs and retains native patch statuses. A private compiler emitter constructs a SysV x64 handler candidate preserving bounded GPR/flags, x87/MXCSR, YMM and errno state around a strong resident callback dependency. Missing collector implementation fails linkage. Neither the fixture nor the emitter advertises a qualified profile. Production provider selection, actual callback closure exclusion, whole-trampoline behavior and nonallocating collector admission remain gates.

The [Windows graph audit](xray_windows_off_graph_review_2026-11-03.sdn) distinguishes compiler conditional preprocessing from the CLI's earlier raw import scan. Physical staging contains the new Linux leaf; it does not fix that scanner or prove a Windows build comparison.

A single isolated C diagnostic executed on Linux AArch64 using installed LLVM23.1.0 (`ea7d852a70e8bdfaf601d6626a760f9771b2c4b4`): 10,000 entry/exit callbacks, correct scalar results and runtime address association, followed by 100 unpatched calls without new callbacks. Exact commands, hashes and retained maps are under `/tmp/parallel-three-tracks-20261103/features/llvm-probe/REPORT.md`. This is installed-toolchain evidence only, not Simple-generated ABI/profile or lifecycle qualification.

Both old startup P1s have an immutable successor source packet at `/tmp/parallel-three-tracks-20261103/features/startup-p1-repair`, manifest SHA-256 `54c6bb1feb08d5831c2565e3ec6acd690475ed4f63ee4096d4a45462af7cf03f`. Review accepted the activation-fence source change, but found the raw overlap correction incomplete: byte-disjoint PT_LOADs can alias after host-page rounding. A revision addressing that remaining P1 is in progress. No packet is integrated because its dependency closure is absent from this Git tree. Tests remain UNRUN; original frozen sources are untouched.

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
