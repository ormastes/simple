# Hosted compiler discovery accepts clang-cl without the C SDK

Status: source correction implemented; admitted compiler verification blocked.
Scope: Windows bootstrap prerequisite for seven-plan items 1 and 4. This does
not resolve the separate full-compiler host-identity admission failure.

## Observed failure

A bounded diagnostic using the preserved rejected Stage 2 image from the
[Windows investigation](../../03_plan/evidence/seven_plans/windows/bootstrap_readiness_2026-09-29.md)
selected `C:/llvm-23/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe`:

```text
[CC-VERIFY] .../clang-cl.exe: exit=0 obj_exists=true
[RT-COMPILE] cc=.../clang-cl.exe
error: in-process native-build: LLVM native linking failed: Runtime compilation failed: Failed to compile runtime.c:
src/runtime/runtime_memtrack.h(20,10): fatal error: 'stdlib.h' file not found
```

The discovery probe compiled only `int main(void) { return 0; }`. LLVM can emit
that object without a hosted C SDK, so success did not establish the minimum
header availability that the runtime itself requires. Automatic discovery
stopped at this candidate instead of checking later candidates.

## Correction

`runtime_compiler._cc_verify_compiles` now includes `<stdlib.h>` in its probe.
It retains the existing compiler invocation, object-existence requirement,
failure diagnostics, cleanup and candidate ordering. This applies to automatic
hosted compiler discovery; explicit overrides keep their existing semantics.
No new compiler, ABI, host or target is admitted by this change.

This is only a header-availability check. It does not certify linker libraries,
runtime features, target compatibility, compiler version or complete SDK health.
Those obligations remain with their existing toolchain and bootstrap gates.

## Focused evidence

On 2026-09-29, the actual probe string was extracted from the changed `.spl`
function into a temporary C file, then compiled using real native tools:

| Invocation | Exit | Object exists | Interpretation |
|---|---:|---|---|
| Installed clang-cl, `/nologo /c /Fo...` | 1 | false | Rejects the observed missing `stdlib.h` SDK |
| Installed MinGW GCC, `-c -o ...` | 0 | true | Positive control with available C headers |
| Same GCC, `-nostdinc -c -o ...` | 1 | false | Rejects deliberately unavailable headers |

The GCC invocations are diagnostic controls, not admission of a compiler to an
MSVC lane. Logs and emitted probe are in
`build/native_probe/seven-plans-windows/hosted-{clangcl,gcc,no-headers}.log`
and `hosted-c-discovery.c`. The probe runs were performed once each.

The Simple discovery function itself has not executed from an admitted rebuilt
compiler. Its SSpec suite and mandatory compiler/lib/MCP/LSP checks remain
TEST_BLOCKED by the unavailable admitted self-hosted CLI. Do not mark this bug
resolved or the seven-item Windows program complete using these tool controls.

## Related bounded trace

A separate diagnostic selected the available GNU compiler explicitly to get
past missing MSVC headers. It reached C runtime compilation and hit its
45-second observation budget at `runtime_audio.c`; the diagnostic process was
terminated deliberately and no compiler descendant remained when checked.
This is neither successful admission nor proof of the original host bug's cause.
No deployment, receipt or shared bootstrap cache was changed.
