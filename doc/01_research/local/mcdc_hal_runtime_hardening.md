<!-- codex-research -->
# Local Research: MC/DC and HAL Runtime Hardening

## Scope and current verdict

The repository has partial condition/decision counting, a manually driven `std.mcdc` analyzer, static AOP weaving, dormant dynload components, a typed HAL capsule, generic counterpart-provider evidence, and structured skip governance. It does not yet have compiler-wide MC/DC independence evidence, a truthful static denominator, native probe lowering, production dynamic aspect activation, an `rt(hal)` provider tag, or typed environment-instruction extraction/replay.

## Coverage producer and denominator

- `src/compiler/10.frontend/core/interpreter/eval.spl:17-94` is the only automatic producer found. It assigns decision/condition IDs, records evaluated atoms, and preserves short circuiting.
- MIR defines `DecisionProbe` and `ConditionProbe`, but `src/compiler/50.mir/mir_coverage_probe_admission.spl:94-139` rejects them because backend lowering is absent. LLVM, C, native x86, and MIR interpreter paths remain unsupported.
- `src/runtime/runtime_coverage_core.c:13-26,90-135` and `src/compiler_rust/runtime/src/coverage.rs:18-64` retain aggregate true/false counts, not per-evaluation condition vectors plus final decision outcomes. Independence pairs therefore cannot be reconstructed.
- The runtime reports only observed rows; `src/compiler_rust/runtime/src/coverage.rs:129-170` returns 100% for an empty total. No compiler-emitted manifest enumerates all eligible decisions and conditions.
- `src/compiler/90.tools/coverage.spl:121-123` sets total lines equal to hit lines and branch totals to zero, so it cannot act as the release oracle.
- `src/lib/nogc_sync_mut/mcdc.spl` supplies manual decision registration, evaluation recording, masking analysis, reports, and compatibility facades, but it is disconnected from compiler instrumentation.
- `scripts/check/cert/mcdc_instrument.spl` is an interim source rewriter limited to selected block headers and grammar shapes; it is unsuitable as the complete language implementation.

## Performance and aspect modes

- Disabled interpreter probes call `rt_coverage_enabled()` on every probe, and the C implementation performs `getenv`/comparison again. Enabled recording locks and reallocates/copies, so neither disabled nor enabled hot paths meet the requested contract.
- Static HIR AOP weaving in `src/compiler/35.semantics/aspect_weave.spl:18-25,110-164` inserts direct calls and naturally has zero cost when omitted.
- Dynamic components (`JoinpointSlotTable`, `AdviceBindingRegistry`, `PackIndexCache`) exist under `src/compiler/99.loader/`, but no production compiler path emits their callsites or activates packs. Startup preload is explicitly absent in `aspect_pack_io.spl:149-157`.
- Dynamic slots necessarily impose an indirect dispatch when emitted. The correct contract is therefore exact zero overhead only for static-off, bounded idle overhead for dynamic-disarmed, and measured active overhead for static-on/dynamic-armed.
- `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md` and `doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md` are the canonical existing design/active plan and must be extended, not replaced.

## Runtime/HAL provider comparison

- `src/lib/nogc_sync_mut/hal/` provides typed MMIO, IRQ, DMA, and QEMU-mock surfaces, but no `rt(hal)` tag or provider policy. DMA free/sync are no-ops and hosted IRQ behavior is stubbed.
- Current native runtime selection distinguishes `simple-core` and `core-c-bootstrap`; Rust-hosted aliases fail closed. Runtime symbol ownership is archive/link based rather than operation-tag based (`doc/04_architecture/runtime/rt_symbol_ownership.md`).
- `std.nogc_sync_mut.spec.evidence.counterpart` already registers N-way provider/component/boundary adapters and preserves unavailable required sources. Its runner is sequential and some transports remain unavailable, but it is the strongest reusable comparison base.
- Existing canonical dual-backend modes are `alpha` (run both and stop on diff), `beta` (run both and report), and `normal` (preferred only). The new N-way provider layer should preserve those semantics.
- `src/app/io/mod.spl` is a compatibility shim; new environment and process work belongs in std/HAL owner modules, not app-local raw runtime calls.

## Environment instructions and exclusions

- Test discovery has file-level tags/platform/baremetal metadata in `test_manifest.spl` and `test_manifest_scanner.spl`, with path/header-based QEMU classification. There is no typed environment-interaction instruction model.
- `std.spec.skip(name, reason)` and `skip_via_ref` provide free-text and structured SDN governance. Structured records can carry category, owner, requirement, alternative evidence, venue, expiry, and issue.
- Compile-mode injected skip behavior is weaker and print-oriented; coverage does not consume skip records or map an exclusion to static decision/condition identities.
- The implementation should converge on one structured exclusion record, preserve gross and eligible denominators, and reject locally producible, blank, generic, stale, or unknown exclusions.

## Owner-boundary decisions for design

- Compiler front end/MIR owns Boolean decomposition, stable static manifests, and compile-time static-off erasure.
- Backend lowering owns compact probe emission; the coverage collector owns bounded vector/mask events and deterministic merge.
- The canonical aspect loader owns dynamic activation and patchpoint settlement; MC/DC must be a consumer, not a private loader.
- Std HAL plus counterpart evidence owns tags, provider adapters, normalization, comparison, and parent-authoritative commit.
- Test-runner environment infrastructure owns typed extraction/execution and structured unsupported reporting.
- Existing env/process facades remain the only authorized environment boundary.
- Runtime/HAL operations need an assurance classification in their canonical declarations. Mission-critical paths require caller-owned/fixed-capacity storage rather than hidden heap growth; existing no-op DMA/IRQ gaps and allocation-returning interfaces make a broad interface audit unavoidable.

## Existing evidence blockers

- `doc/06_spec/test/mcdc_spec.md` documents a pending executable body while its summary claims no pending scenarios; it must be regenerated and manually reviewed.
- `doc/09_report/aspect_dynload_hal_runtime_status_2026-08-19.md` already rejects current HAL 100% claims as untrustworthy.
- Exact numeric performance/memory limits and the unique-cause versus masking policy remain user decisions.
- The warning duration and exact milestone that promotes missing/lower assurance classifications to errors remain user decisions.
