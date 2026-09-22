# Phase 2 Vulkan readback loader ABI

## Scope and cause

The core-C GPU loader lacked seven array/readback exports needed by the Phase 2
test runner. A subsequent composition review found an eighth:
`rt_vulkan_readback_u32_checksum` disappears when `SIMPLE_RUNTIME_DYNLOAD_OWNER`
removes the old unavailable weak fallback. All eight take native core-C values
where declared as arrays; those values cannot be passed to a Rust provider's
boxed `RuntimeValue` ABI.

This is sidecar A of the frozen GPU loader partition. Original manifest SHA-256
was `c56264da3bbbeb33286fb86b0b160b012a92006ebd382662c8a86cdfccf5fc5a`.
The authorized eighth-row correction uses
`c82c7448c210276a5633d8e973e359f4069ebe8e834dab81b5b46c164c5b04ef`.
Merge owner: `/root/stage2_after_backend_receiver`. Sidecar branch baseline:
`e6ffda6849e6aa7fe01a7d23ddc71e9773286532`.

## Boundary implementation

`src/runtime/runtime_gpu_vulkan_readback_private.h` is the only production
fragment owned here. The merge owner includes it from `runtime_dynload.c` and
supplies the canonical `rt_array_i64_validate` and
`rt_array_i64_copy_checked` helpers in `runtime_native.c` / `runtime.h`.
This sidecar does not alter the registry, provider requirements, or shared loader.

- Every provider invocation acquires/releases the existing call pin.
- Byte destinations use checked core-C byte APIs, supporting packed `[u8]`
  and tagged byte slots. Integer inputs use the registered integer-array APIs;
  there are no private array-header casts.
- Transfers are bounded at the existing 2 GiB provider limit. Products,
  offset sums and strided end offsets are checked before allocation or calls.
- Regions encode LE i64 tuples; the effective provider bounds are 256 regions
  and 16,384 cumulative rows (`vulkan/buffer.rs`, stricter than its raw wrapper).
- Only successful raw readback commits into caller storage. Partial provider
  writes followed by failure leave destinations and their tails unchanged.
- Word upload accepts signed i32 representations through `u32::MAX`, packing
  four LE bytes per element. Output words decode LE without sign extension.
- Unavailable returned arrays are owned, genuine core-C empty arrays;
  checksum failure remains `-1`, distinguishable from valid zero.
- With at most `2^29` words, the checksum sum is below `2^61`; reducing once
  modulo 2147483647 equals the canonical per-element fold without overflow.

The in-flight unload test uses a worker-owned scalar checksum result. A
provider-local atomic handshake keeps its lease live while the parent attempts
unload; the parent reads the result only after joining the worker. No native
array is shared with that worker.

## Retained verification — one cycle

Host: macOS arm64. LLVM: 23.1.1. Producer: admitted pure-Simple **Stage 2**
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-admitted/simple`.
SHA-256: `0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`.
Its adjacent `admission.env` is copied into the evidence directory. The runtime
capsule is the same P0 output's `phase-runtime-capsules/stage2/<producer-sha>`.
The command invokes that admitted Stage 2 executable, but its explicit
`--entry --emit-archive` route delegates through `run_rt_native_build` to the
Rust native-build ABI (`bootstrap_main.spl:384-389`). This proves actual compiled
Simple array interoperability, **not the self-hosted frontend**. The retained
launch script does not explicitly set `SIMPLE_NATIVE_BUILD_RUST`; route identity
comes from the explicit-entry dispatch, not an inferred environment value.

Evidence root:
`/Users/ormastes/simple-tmp/phase2-gpu-vulkan-readback-20260923/build/native_probe/phase2_gpu_vulkan_readback/cycle1`.
The retained launch script is `build/run-phase2-gpu-vulkan-readback-cycle1.sh`.

- Native fixture archive: 1 compiled, 0 cached, 0 failed; 9 KB. Compile/link
  driver time 0.2s. `SIMPLE_NO_STUB_FALLBACK=1`, one thread, private cache.
- Actual native Simple fixture called all eight adapters with typed arrays and
  returned **0**. The C harness asserts that result, lengths, byte/word contents,
  unchanged failure destinations, and checksum values.
- Synthetic provider: successful contiguous/prefix, strided and region copies;
  signed/u32 maximum upload, high-bit readback, genuine empty outputs,
  unavailable sentinels, malformed types/counts/offsets/strides/overflow,
  256/257 regions, 16,384/16,385 cumulative rows, and failed provider writes.
- Invalid requests did not increase the provider call counter. Unload during a
  pinned call was refused; unload after join succeeded. Returned data remained
  readable after unload.
- The baseline loader failed to link with all eight missing symbols, retained
  in `check/baseline-link.log`; the corrected adapter linked and executed.
- Source hashes before and after execution cover the shared runtime/header,
  loader, private fragment, wrapper, C fixture, native fixture and checker.
  Producer and archive hashes are recorded separately.
- Compile peak sampled tree RSS: 78,320 KiB. C build plus all checks peak:
  152,944 KiB. Both receipts: exit 0, quiescent 1, observer errors 0, sampled cap
  enforced at 5,859,375 KiB, `hard_memory_limit=0`.
- Synthetic 10,000 six-byte copies: 2.177 ms CPU (C harness), 2.145 ms (harness
  also executing native fixture). Twenty 800x600 destination readbacks:
  112.717 / 117.833 ms CPU, checksum 634340096. These are local synthetic CPU
  observations, not device latency or a before/after GPU performance claim.

Reproduction: compile `phase2_gpu_vulkan_readback_native.spl` with the admitted
producer using `native-build --emit-archive --no-mangle --backend cranelift
--entry <fixture> --entry-closure --runtime-bundle core-c-bootstrap
--runtime-path <verified-capsule> --threads 1 --cache-dir <private-cache>
-o <fixture.a>`. Then run
`GPU_READBACK_OWNER_ROOT=<integrated-runtime-root>
GPU_READBACK_SIMPLE_ARCHIVE=<fixture.a>
GPU_READBACK_BASELINE_ROOT=<baseline-root>
sh scripts/check/check-phase2-gpu-vulkan-readback.shs <new-evidence-directory>`
under the canonical sampled RSS watchdog. Omitting the archive runs only the
C ABI tier; it must not be reported as native Simple-boundary proof.

## Claim boundary

Independent Astra-high review (`/root/stage2_after_native_cache/gpu_readback_review`):
**STATUS: PASS** for the scoped synthetic ABI and native Simple boundary;
zero P0/P1 findings and no concrete merge blocker. Runtime evidence was reviewed
without rerunning passing checks.

Focused synthetic C and native Simple ABI checks passed. Physical Vulkan,
the self-hosted frontend, full test-runner linkage/execution, the compiler matrix, Phase 2 completion and
Stage 3 remain separate merge-owner/root gates. No bootstrap or push occurred.
The shared integer helpers' direct rejection/no-partial-write tests belong to
the merge owner's combined check, not this sidecar's new source ownership.
