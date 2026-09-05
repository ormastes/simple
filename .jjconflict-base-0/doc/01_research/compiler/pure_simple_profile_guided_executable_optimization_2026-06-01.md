<!-- codex-research -->
# Pure Simple Profile-Guided Executable Optimization Local Research

Date: 2026-06-01

Scope: persistent profile loader, native optimization, pure-Simple BOLT-like
executable optimization, and bare-metal counter profiling with software
breakpoints.

## Existing Repo Surfaces

### Interpreter And JIT Counters

`src/compiler/95.interp/execution/tiered_jit.spl` already exposes
`FunctionProfile.call_count`, `TieredJitConfig.tier1_threshold`, and
`TieredJitConfig.tier2_threshold`. `jit_hotspot_profile_facts(...)` emits
`profile.hot_count` only after the profile count reaches the tier-1 threshold
and only combines it with `typed_mir` and `safe_deopt` facts.

Implication: counter-based interpreter/JIT optimization exists, but it is
in-memory and not yet a persistent profile loader.

### Persistent `.sprof` Schema Contract

The previous roadmap slice selected a schema-first `.sprof` path. The intended
contract is in the roadmap/design artifacts, and the implementation target is
`src/app/optimize/sprof_schema.spl` when present in the active working copy.

Implication: the next real implementation step is loader/writer/merge plumbing,
not redefining the field list.

### Native Executable Optimization

`src/app/compile/native.spl` routes LLVM-family backends through
`aot_native_file_with_backend(...)` and maps compile optimization levels to
`-O0`, `-O1`, `-O2`, and `-O3` for C/native fallback builds. It also supports
ThinLTO flags and target `-march` in the native compile command path.

`src/compiler_rust/compiler/src/optimizations/mod.rs` defines native
optimization profiles, with tests asserting that the default native executable
profile is aggressive and that aggressive enables layout optimization.

Implication: Simple has native executable optimization knobs, but not an
end-to-end profile-guided executable optimizer.

### Loader And Executable Startup

`src/compiler_rust/loader/src/startup.rs` is the startup-only loader for
settlement executables. It loads executable settlement data, maps code/data
memory, exposes entry/function pointers, and executes an entry point.

Implication: loader-time profile consumption belongs at startup or
optimize-app time, not in hot request handlers.

### Bare-Metal Counter Profiling

Local search did not find a mature bare-metal software-breakpoint counter
profiler. Existing bare-metal docs and QEMU/driver tests provide adjacent
surfaces, but no unified breakpoint-counter lifecycle appears implemented.

Implication: this needs a new MDSOC+ capsule with strict arm/disarm policy and
fallback timer/sampling paths.

## Gaps

1. `.sprof` loader/writer/merge: schema exists/planned, but profile file
   ingestion and validation are not yet connected to startup, optimize-app, or
   JIT planning.
2. Native counters: native executables do not yet emit Simple-owned block,
   function, edge, or call-path counters into `.sprof`.
3. Pure-Simple BOLT-like optimizer: no Simple-owned post-link executable layout
   optimizer exists. LLVM BOLT should remain a reference only, not a dependency.
4. Bare-metal software-breakpoint counters: no explicit patch/trap/restore
   counter lifecycle exists for bare-metal targets.
5. Slow-running breakpoint risk: no current policy removes or backs off
   breakpoint counters when trap overhead distorts execution.

## Recommended Work Split

| Lane | Owner Scope | First Deliverable |
|------|-------------|-------------------|
| A `.sprof` loader | `src/app/optimize`, loader startup docs/tests | validate/load/merge profile summaries without hot-path reads |
| B native counters | native compile/runtime boundary | function/block/edge counter ABI and `.sprof` writer hook |
| C pure Simple executable optimizer | optimize app + settlement/native metadata | reorder functions/basic blocks from `.sprof` counts |
| D bare-metal counters | OS/bare-metal debug capsule | software-breakpoint counter lifecycle with auto-disarm |
| E verification | SPipe/manual docs/perf reports | workload, overhead, RSS, and call-path evidence gates |

## Non-Negotiable Safety Rules

- Profile data is evidence, not semantic proof.
- `.sprof` load must be opt-in until startup/RSS overhead is measured.
- Hot request paths must not reread profiles, shell out, or scan the tree.
- Bare-metal breakpoint counters must be removable and must degrade to
  sampling/timer counters when overhead exceeds budget.
- Executable rewriting must be reproducible and must preserve symbol,
  relocation, unwind, and entry metadata.
