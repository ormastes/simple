# MIR shard worker commit blowup on full-closure native-build (3004 modules)

Date: 2026-11-05
Host: Windows 11, 31.7 GiB RAM (33,195,332 KiB), llvm-mingw 20260922, cranelift
Lane: wave-1 verification — full CLI built from the admitted stage-2 compiler
(`native-build --entry src/app/cli/main.spl --entry-closure`, sources
src/compositions/cuda_disabled + src/compiler + src/app + src/lib + src/os +
src/plugins, --threads 4, cache = stage2-native-cache)

## Observation

Parse, surface_build, surface_freeze, and the first HIR pass completed
(3004/3004, 0 failed). The MIR shard phase then collapsed:

```
[mir-shard] owner=0/1@0 status=CRASH exit=-1073741819 claimed=1 sealed=1   (0xC0000005 access violation)
[mir-shard] owner=0/1@1 status=CRASH exit=-1073740791 claimed=0 sealed=0
  (allocation-failure abort 0xC0000409: host commit limit exhausted;
   set SIMPLE_MIR_SHARD_WORKER_KB to at least the measured worker peak commit)
memory allocation of 35651600 bytes failed
[mir-shard] measured worker peak commit=17754600 kB (static estimate 9000000 kB,
  previous run 855720 kB)
[mir-shard] completed_workers=0 failed_workers=3 failed_modules=3004
```

Every module reports BLOCKED behind the two crashed workers; link and
publication are blocked.

## Root cause (resource, with an open code question)

Primary: one MIR shard worker grew to ~17.7 GiB commit on this host, which
exhausted the Windows commit limit and aborted allocation (0xC0000409).
The same worker measured 855 MiB on a previous run and the static estimate
is 9 GiB — a 20x variance that tracks with the larger module closure
(3004 modules here vs 1569 in the stage-2 build, the extra ~1400 coming from
src/os + src/plugins + src/compositions/cuda_disabled).

Open question: the FIRST crash was an access violation (0xC0000005) in a
worker that had claimed and sealed work, before the commit exhaustion. That
may be an independent latent defect in the self-hosted MIR lowering
(crash locus reported as compiler.mir._MirLoweringExpr.switch_operators_calls,
possibly while lowering plugins.backend_vulkan/vhdl modules that are outside
the stage-2 closure and therefore never exercised by the admitted compiler's
sanity matrix). Not shown to be related to the wave-1 stronger-types changes
(stage-2 admission and its full sanity matrix passed with those changes).

## Mitigation applied

Relaunch with the scheduler hint from the crash message and reduced
parallelism:

    SIMPLE_MIR_SHARD_WORKER_KB=18177000   # >= measured worker peak commit
    --threads 2

## Suggested direction

1. Bound or shard the MIR worker's per-module accumulation (20x variance
   across runs needs an explanation; a memory profile of the worker over the
   3004-module closure would show whether growth is cache, arenas, or a leak).
2. Make the access-violation first crash reproducible in isolation
   (SIMPLE_MIR_SHARD_ONLY_PATHS can restrict the shard to the vulkan/vhdl
   plugin modules) to separate the code defect from the resource crash.
3. Consider admitting the os/plugins closure into the stage-2 sanity matrix
   so resource/code defects of this class surface during admission instead
   of in downstream tool builds.

## Status

OPEN (mitigation retry in flight in the work/simple-hardening-release-20261013
lane; the stage-2 trust root itself remains admitted and unaffected).

## Addendum (same day, test-runner closure)

The reduced-closure standalone test-runner build (322 modules, sources
src/compiler + src/app + src/lib, entry src/app/test_runner_new/main.spl)
fits memory comfortably (MIR/codegen RSS ~5 GiB) but exposed a second
pathology in the self-hosted codegen path: `native_compile` spent 40+
minutes on a single module (indicator `lib.nogc_async_mut.sosix.stdio`,
a 41-line source file, worker ~1300s CPU and climbing). Whether the
indicator lags the real in-flight module or a 41-line extern-heavy file
genuinely expands into a codegen super-linear cliff, single-module
compile times of this magnitude make from-scratch tool builds
impractical on this host. Recommended follow-up: capture a profile of
the codegen worker (module attribution, MIR instruction count per
module) and compare against the LLVM backend, which the matrix
benchmarked as the default for good reason.

## Addendum 2: core-c-bootstrap link lib gap (same day)

Standalone self-hosted `native-build` on hosted mingw with
`--runtime-bundle core-c-bootstrap` fails at link with undefined system
symbols (BCrypt*, TransmitFile, D3D11*, WinHttp*): the complete windows
library list in `linker/_LinkerWrapper/native_all_support.spl` is gated
behind `native_all_input_present`, and
`native_all_allowed_for_runtime_bundle` explicitly returns false for
`core-c-bootstrap`, so the runtime objects are linked without the system
libs. Supplying `--runtime-path <stage2-runtime-authority>` alone does
not help while the bundle gate stays closed; using the default bundle
(native_all admitted) with the same runtime path is the working
configuration for standalone tool builds. Whether the bootstrap lane's
own core-c-bootstrap links pass because of session env or whether this
gate is an oversight for standalone hosted builds is worth a follow-up.
