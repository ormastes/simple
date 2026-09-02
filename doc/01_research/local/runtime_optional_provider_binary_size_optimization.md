# Runtime Optional Provider and Binary-Size Optimization — Local Research

## Scope

Preserve every Simple language and architecture feature while reducing script-runtime loading and native executable closure. Optional facilities must be demand-loaded, pure-Simple implementations must be preferred under a reversible dual-provider policy, and release-small output must omit exception, unwind, and RTTI machinery when the admitted closure does not need them.

## Current Evidence

- `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md` records eager dynSMF startup and seven general libraries historically marked for default autoload.
- The 2026-06-05 cross-language report produced a 38.3 KB Simple native hello versus 15.6 KB C, proving that sub-40 KB output is feasible.
- Later 2.7–6.3 MB hello artifacts show that runtime/tool closure and link composition can regress by two orders of magnitude.
- The current macOS runnable interpreter diagnostic used about 18.0 MiB RSS versus Python 3.14 at 14.6 MiB. DYLD tracing showed optional crypto, SQLite, compression, terminal, Swift/framework, and graphics dependencies entering the process.
- `src/compiler/80.driver/driver_aot_native_output.spl` already has entry-closure, provider identity, runtime capsule, and native-link ownership surfaces suitable for enforcing the smaller closure.
- Existing provider and pure-Simple policies already reject silent SFFI substitution; this work extends them with stability-qualified dual mode rather than removing foreign providers.

## Root Causes

1. Provider registration and provider loading are insufficiently separated.
2. Optional libraries can become startup/link roots through manifests, constructors, broad archives, visible exports, or default-autoload policy.
3. Coarse runtime object sections make one required symbol retain unrelated helpers.
4. Release profiles do not express a closed, evidence-backed exception/unwind/RTTI requirement set.
5. Pure-Simple implementations and foreign providers lack one stability ledger and deterministic selection contract.
6. Binary-size reports do not retain linker maps, removed-section logs, symbol-size rankings, dynamic dependency lists, or closure reasons.

## Historical Size Interpretation

The lost 38.3 KB artifact cannot be attributed byte-for-byte because its map and symbol reports were not retained. Its approximately 22.7 KB excess over C most plausibly came from runtime entry/exit, tagged-value and generic print paths, unwind metadata, dynamic symbols/relocations, coarse runtime sections, and compatibility helpers. GC is not a sufficient explanation because the selected default is NoGC and a no-allocation hello should not admit a collector.

## Constraints

- No feature removal and no architecture narrowing.
- Dynamic loading is demand-driven, not a correctness fallback.
- A provider may load only after exact capability, ABI, target, digest, and policy admission.
- Pure-Simple is preferred only after stability qualification; foreign providers remain available during dual mode.
- Debuggability and profiling remain available in debug/release profiles even when release-small omits their metadata.
- Unsupported unwind/RTTI removal fails closed instead of producing a subtly broken binary.
