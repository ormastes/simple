# Feature Expert: Native Build

## What this is
Compilation of Simple source code to native binaries: the `bin/simple native-build` pipeline, encompassing closure discovery, native codegen, C FFI linkage, symbol resolution, and runtime library integration for host platforms.

## Source of truth
- **Observability:** Environment knobs for progress + diagnostics:
  - `--diagnostics=test` — progress and coarse phase timing, without parser trace
  - `--diagnostics=debug` (or bare `--diagnostics`) — test mode plus detailed
    trace, successful LLVM IR retention, and memory snapshots
  - `SIMPLE_COMPILER_TRACE=1` — detailed phase transitions
  - `SIMPLE_COMPILER_PHASE_PROFILE=1` — per-phase timings
  - `SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE=debug|test` — environment equivalent
  - `--log off` controls **guest-kernel logging, NOT build verbosity**
  - Per-line flush now landed (see `doc/08_tracking/bug/simpleos_harness_silent_native_build_2026-07-26.md`)
  - AOP call/assignment logs are not implied; enable them separately only for
    a scoped weave investigation because they can materially affect runtime.
  - Isolated diagnostic sweeps use
    `--diagnostic-child-compiler=/absolute/path/to/simple`; never rely on an
    ambiguous cwd-relative worker identity.

## Code map
| File | Role |
|---|---|
| `src/compiler/80.driver/driver_native_build.spl` | Entry point, closure discovery, codegen dispatch |
| `src/compiler/80.driver/native_build_closure.spl` | Recursive import tracer (plain `use` only, NOT `export use` shims) |
| `src/compiler/70.backend/backend_llvm.spl` | LLVM codegen backend selection |
| `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` | Cranelift JIT backend (host-arch detection: `host_arch()`) |

Specs: `test/01_unit/compiler/80.driver/driver_native_build_spec.spl`.

## Cache: incremental persistence (2026-07-26)
- **Index now writes to disk every 5 modules** — timeout no longer loses work
  (`doc/08_tracking/bug/native_build_cache_never_written_on_timeout_2026-07-26.md`)
- **Seed-lane cache identity quirk:** pre-stage4 seed binaries have an uncacheable
  identity (cache validation fails on seed-compiled artifacts; rebuild after
  stage4 redeploy)
- **Zero-hash never accepted:** compile-options mismatch triggers plain cache miss →
  rebuild (not a silent fallback)

## Known open defects (2026-07-26)
| Bug | Scope | Link |
|---|---|---|
| LLVM-lane nil-self miscompile | Native-compiled code crashes on nil-receiver | `native_build_nil_receiver_crash_2026-07-25.md` |
| Parser ~100cps collapse | Native-build lane only, full project parse halts | `native_build_parser_100cps_regression_2026-07-26.md` |
| Nested-call `.replace` resolution | Bare string method in nested calls rebinds to wrong receiver | `native_build_nested_replace_method_resolution_2026-07-26.md` |

## Closure discovery limitation
The recursive tracer (`.spl` → closure) follows plain `use` imports only — does NOT
traverse `export use` shims. If re-exporting driver or lowering modules, closure must
be assembled manually or tracer extended.

## Runtime linkage (hosted paths)
**Critical:** `SIMPLE_RUNTIME_PATH` env var **MUST** be set to seed target directory
for hosted native-build linking. The `--runtime-path` CLI flag alone does NOT set the
env var. Host-side wrappers must explicitly pass both:
```
SIMPLE_RUNTIME_PATH="path/to/seed/target" bin/simple native-build ...
```
Hosted link backfills `rt_*` externs from `libsimple_native_all.a` only if the env var
points to correct seed target.

## Update Rule
After native-build defects, closure-discovery changes, or cache logic shifts, refresh
this skill with new open-bug links and concrete gotchas.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
