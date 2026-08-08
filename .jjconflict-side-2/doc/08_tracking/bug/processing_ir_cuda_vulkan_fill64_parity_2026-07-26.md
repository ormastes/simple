# ProcessingIR CUDA/Vulkan Fill64 Parity

- **Status:** open
- **Host:** Linux x86_64 with CUDA and Vulkan devices

## Measured blockers

The source-matched native Vulkan executor passes the existing eight-element
`FillU32(0x01020304)` probe. Expanding the same probe to 64 elements exposed a
size-dependent device result:

```text
completed=true reason=ok values=64
requested_count=64 requested_value=16909060
first_value=135272480 checksum=8657438720 mismatches=64
handle=1 identity=1
```

The requested IR is correct. The first returned value is `0x08101820`, the
aggregate checksum is exactly eight times expected, and all 64 values mismatch.
Importing Engine2D's `_pack_clear_pc` directly into the ProcessingIR executor
then caused a native startup SIGSEGV, consistent with introducing the existing
`backend_vulkan` / `backend_vulkan_helpers` module cycle. The three-cycle
verify/fix cap was reached, so no further live retry was made.

The retained CUDA receipt proves generated CUDA C/PTX and exact device
readback, but it does not call `processing_ir_execute_cuda`. It is valid
lower-level evidence, not ProcessingIR backend parity evidence.

A new direct CUDA native probe initially failed at module load because the
Simple wrapper passed native text to C-string runtime entry points. Routing
compiled calls through the existing length-tracked PTX and kernel-name ABIs
fixed module load and launch. CUDA then completed device readback but returned
the same 64 mismatches and checksum `8657438720` as Vulkan. Exact-size result
array allocation did not change either result and was removed.

The focused native `processing_u32_array_transport_probe.spl` isolated the
shared result:

```text
case=local-push  first=135272480 iterator_mismatches=0 indexed_mismatches=64
case=local-fixed first=135272480 iterator_mismatches=0 indexed_mismatches=64
case=returned    first=135272480 iterator_mismatches=0 indexed_mismatches=64
case=wrapped     first=135272480 iterator_mismatches=0 indexed_mismatches=64
```

Iteration decodes all 64 host-generated values exactly while direct indexing
returns each tagged integer (`value << 3`). Disassembly confirms iteration calls
`rt_index_get` and untags its result, while direct indexing loads tagged array
storage without an untag. This reproduces the 8x symptom without a GPU and
narrows the blocker to the retained compiler's native read path. It does not
prove that CUDA/Vulkan device bytes were correct.

Current source marks array parameters as runtime arrays and routes that path
through `rt_array_get` plus `decode_runtime_value`; built-in `u32` is already a
primitive HIR type, so the earlier proposed struct-provenance guard was
withdrawn. A fresh source-matched compiler is required to determine whether the
retained compiler is stale or current lowering still loses runtime-array
classification.

The 2026-07-27 bounded incremental regeneration used the focused compiler
route. The CLI entry parsed current source until the retained parser rejected a
named tuple expression in an unrelated Office closure. The narrower positional
`bootstrap_main.spl` route avoided Office but stopped on the retained parser's
known `pub mod` gap. One temporary private-`mod` source projection parsed the
compiler closure, then the process terminated while lowering
`run_compile_bootstrap`; canonical `pub mod` source was restored immediately.
The three-cycle cap is exhausted.

The same session reran live device evidence. Standalone CUDA
fill/copy/alpha/scroll readback passes with two devices, positive identity,
exact checksum, and zero mismatches. The later ProcessingIR CUDA probe reaches
device readback with positive handle/identity and `cpu_fallback=false`, but
still reports 64 mismatches and checksum `8657438720`. The retained
source-matched Vulkan evidence reaches `backend_name=vulkan` and strict
creation before crashing; the later ProcessingIR Vulkan probe also crashes
before publishing a receipt. A canonical `--phase=none` GDB run of the later
probe places that crash in `common.string_core.str_starts_with`; disassembly
shows the generated helper recursively calls itself instead of
`rt_string_starts_with`. The probe accepts only six fixed phase tokens, so its
argument parser now matches those complete tokens directly and no longer
depends on `starts_with` or slicing. At that point the native probe still
needed rebuilding before Vulkan parity could be measured.

Three bounded probe rebuild attempts then stopped before producing a candidate:
the first found unrelated full-app module-name collisions; the second used an
archive-only runtime overlay; the third passed the Cargo target parent rather
than its `bootstrap` output directory. The latter contains
`libsimple_runtime.a` and `libsimple_runtime.rlib`, but the linker diagnostic
persisted because its hosted owner is a different crate.

The retained backend actually requires the Vulkan `libsimple_runtime.a` and
the separate `libspl_hosted_runtime-*.rlib`. A two-symlink build projection
provided those existing artifacts without rebuilding either runtime. The
fixed-token probe then rebuilt incrementally (`1 compiled, 31 cached`) and
reached a truthful backend result: Vulkan completed with positive
handle/identity, while stale direct indexing alone reported values in tagged
form. Raising the request from 8 to 64 values and changing the evidence
consumer to language-level iteration produced an exact 64-value receipt, and
the canonical wrapper passed all six isolated processes:

```text
phase=none        completed=true  reason=ok                      values=64 values_exact=true handle=1 identity=1
phase=unavailable completed=false reason=vulkan-unavailable      values=0  handle=0 identity=0
phase=init        completed=false reason=vulkan-init-failed      values=0  handle=0 identity=0
phase=submit      completed=false reason=vulkan-submit-failed    values=0  handle=0 identity=0
phase=readback    completed=false reason=vulkan-readback-failed  values=0  handle=0 identity=0
phase=mismatch    completed=false reason=checksum-mismatch       values=0  handle=0 identity=0
```

This closes Linux Vulkan backend execution and fault injection. It does not
close direct array indexing: that path still exposes the retained compiler's
tagged-value defect.

The direct CUDA ProcessingIR consumer now validates the returned values through
language-level iteration. Its retained native candidate passes the same
64-element request with exact checksum, zero mismatches, positive
handle/identity, `readback_source=device_readback`, and `cpu_fallback=false`.
The aggregate native gate runs that CUDA receipt and the six-case Vulkan wrapper
in one fail-closed process:

```text
PROCESSING_CUDA_NATIVE status=pass count=64 actual_checksum=1082179840 mismatch_count=0 values_exact=true backend=cuda readback_source=device_readback handle=1 identity=1002905313239842438 cpu_fallback=false
processing_vulkan_fault_native_status=pass
processing_cuda_vulkan_native_parity_status=pass
```

This closes iterator-based Linux CUDA/Vulkan ProcessingIR parity for retained
native candidates. It does not prove source-matched compiler freshness or
repair direct indexed `[u32]` reads.

CUDA identity was a separate three-bit tag-width overflow: the UUID hash used
the full positive 63-bit range, so native Simple tagging could make it negative.
The Rust runtime and generated C evidence producer now share a positive 60-bit
mask. The focused native Simple probe passes with identity
`1002905313239842438`, and the live generated CUDA checker reports two distinct
positive identities plus exact fill/copy/alpha/scroll device readback.
This width change intentionally changes previously recorded 63-bit identities;
cross-version receipts and identity-keyed caches must not compare old and new
values as the same algorithm version.

## Current-source Vulkan result

The Vulkan-enabled runtime archive and strict 32-module probe were rebuilt from
the current source tree without bootstrap or generated-stub fallback. The
first current-source gate passed exact 64-value readback and all five fault
phases but retained identity `1`. A known `"abc"` hash vector proved the shared
Simple hash itself after replacing tagged direct indexing with character
iteration; the remaining sentinel came from hashing runtime-returned device
text across the native ABI.

Selected-device fingerprinting now stays in the Rust Vulkan runtime that owns
the physical-device properties and returns one numeric token through SFFI. Its
focused ASCII/surrogate test passes. The final canonical gate passes:

```text
phase=none        completed=true  values=64 values_exact=true hash_sanity=true handle=666008366 identity=666008366
phase=unavailable completed=false reason=vulkan-unavailable      values=0 handle=0 identity=0
phase=init        completed=false reason=vulkan-init-failed      values=0 handle=0 identity=0
phase=submit      completed=false reason=vulkan-submit-failed    values=0 handle=0 identity=0
phase=readback    completed=false reason=vulkan-readback-failed  values=0 handle=0 identity=0
phase=mismatch    completed=false reason=checksum-mismatch       values=0 handle=0 identity=0
```

Identity `666008366` matches the enumerated NVIDIA RTX A6000 device/driver
property tuple retained in `evidence-provenance-current-source.env`. That file
also names explicit live and integration source manifests and binds their
SHA-256 digests to the runtime archive, probe, and wrapper log. The runtime
hash unit and compiler/common Cargo check pass. Supplemental bootstrap-seed
interpreter runs pass the source contract 3/3, shared hash vectors 4/4, Vulkan
metadata contract 1/1, and Metal identity contract 2/2; they are not treated
as canonical self-hosted release evidence.

## Remaining repair

On 2026-07-29, the committed mem-guard allocation path was found to call a
missing runtime heap-owner accessor. The runtime now exposes its existing
thread-local owner ID, and compiler unit compilation advances past that former
hard error. A focused MIR regression now requires direct indexing of a `[u32]`
parameter to use `rt_typed_words_u32_at`, narrow 64-to-32 unsigned, and avoid
boxed `rt_array_get`/`rt_index_get`. The saturated host consumed the 120-second
runtime and 180-second compiler test bounds before either test executed, so
current-source native behavior remains unproven.

1. Run the focused transport probe with a compiler containing the current
   direct-index lowering and require zero
   iterator and indexed mismatches for all four recorded cases.
2. If direct indexing still loads raw storage, trace the lost runtime-array
   classification and repair the shared Index lowering before backend retries.
3. Preserve exact count/value/checksum, device readback, positive backend
   provenance, no CPU fallback, and current-source freshness in future
   aggregate receipts.

Retained build logs:

- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64-cycle2.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64-cycle3.log`
- `build/simpleos_gpu_host/cuda_fill_native/build-cycle3.log`
- `build/simpleos_gpu_host/cuda_fill_native/build-iter64.log`
- `build/simpleos_gpu_host/cuda_fill_native/wrapper-iter64.log`
- `build/simpleos_gpu_host/processing_cuda_vulkan_native_parity.log`
- `build/simpleos_gpu_host/u32_transport/processing_u32_array_transport_probe`
- `build/simpleos_gpu_host/cuda_identity/cuda_device_identity_probe`
- `build/gpu-goal/source-matched/logs/refresh.log`
- `build/gpu-goal/source-matched/logs/positional-refresh.log`
- `build/gpu-goal/source-matched/logs/positional-refresh-pubmod-bridge.log`
- `build/gpu-goal/final-checks/cuda-live.env`
- `build/gpu-goal/final-checks/cuda-processing-live.log`
- `build/gpu-goal/final-checks/vulkan-source-matched-live.log`
- `build/gpu-goal/final-checks/vulkan-processing-live.log`
- `build/gpu-goal/final-checks/vulkan-processing-phase-none-live.log`
- `build/gpu-goal/final-checks/vulkan-processing-phase-none-gdb.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-fixed-phase-parser.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-fixed-phase-parser-entry-closure.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-fixed-phase-parser-host-gpu.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-fixed-phase-parser-runtime-complete.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-iter64.log`
- `build/simpleos_gpu_host/vulkan_fault_native/wrapper-iter64.log`
- `build/simpleos_gpu_host/vulkan_fault_native/runtime-build-identity-hash.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-current-source-runtime-identity.log`
- `build/simpleos_gpu_host/vulkan_fault_native/wrapper-current-source-runtime-identity.log`
- `build/simpleos_gpu_host/vulkan_fault_native/evidence-provenance-current-source.env`
- `build/simpleos_gpu_host/vulkan_fault_native/evidence-live-source-manifest.sha256`
- `build/simpleos_gpu_host/vulkan_fault_native/evidence-integration-source-manifest.sha256`
- `build/simpleos_gpu_host/vulkan_fault_native/compiler-ffi-registration-check.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-recovery.log`
- `build/simpleos_gpu_host/vulkan_fault_native/wrapper-recovery.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-recovery-cycle2.log`
- `build/simpleos_gpu_host/vulkan_fault_native/wrapper-recovery-cycle2.log`
- `build/simpleos_gpu_host/vulkan_fault_native/evidence-provenance-recovery.env`
- `build/simpleos_gpu_host/vulkan_fault_native/evidence-recovery-source-manifest.sha256`
- `doc/09_report/cuda_generated_2d_readback_2026-07-26.md`

No compiler bootstrap was run.
