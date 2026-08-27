# GPU Provider Intensive Test Evidence

Date: 2026-08-26  
Host scope: Linux x86_64 host-independent native provider fixtures.

Selected requirements: Option A (versioned function table with owned sessions)
and Tier 3 (aggressive throughput).

## Dynamic registry stress

Command:

```text
sh scripts/check/check-gpu-provider-dynload-registry.shs --intensive
```

Result: PASS.

- Complete ABI-v1 CUDA/Vulkan providers admitted; wrong ABI, wrong backend bit,
  incomplete surface, and missing library rejected.
- Provider path containing spaces loaded correctly without a static dependency.
- Environment changes did not replace an admitted provider before unload.
- 64 alternating unload/replacement cycles returned the expected distinct
  device counts, buffer handles, paths, ABI, and backend bits.
- Failed admission remained cached until explicit unload; unload enabled clean
  recovery.
- Unknown backend IDs and empty-path unloaded state failed closed.
- 16 threads completed 16,000 registry/dispatch reads with zero failures.
- The provider exported only `simple_gpu_provider_query_v1`; backend functions
  remained hidden and were dispatched from the admitted table.
- Owned session/submit/wait returned provider/device identity, and unload was
  rejected while the session remained live.
- The typed Simple facade now exposes the admitted provider path and explicit
  unload, allowing environment-selected provider replacement without changing
  or rebuilding the host binary.

## Metal adapter stress

Command:

```text
sh scripts/check/check-metal-provider-dynload-registry.shs --intensive
```

Result: PASS.

- Complete surface admitted; wrong ABI and incomplete surface rejected.
- Embedded-zero RuntimeValue/text payloads remained length-delimited.
- Empty shader source, negative/greater-than-byte array values, and requested
  length mismatches were rejected.
- Failed download preserved caller-owned output.
- 1,000 repeated library/upload/set-byte adapter cycles passed.

## Quality gates

- Shell syntax: PASS.
- Rendering source-coupling working diff: PASS after an exact native-fixture
  exception; copied checkers remain rejected by the modern SSpec regression.
- Changed-test placeholder scan: PASS.
- Generated-spec layout: PASS (`0` executable specs under `doc/06_spec`).
- Diff whitespace/error check: PASS.

## Claim boundary

These tests prove the hosted provider ABI, lifecycle, concurrency, and core
adapters. They do not replace physical Vulkan/CUDA submission/readback, native
macOS Metal readback, GUI/Web/WM production-route evidence, or real web/DB
kernel execution. The new modern SSpec sources require an admitted pure-Simple
Stage4 runner and generated manuals before final verification.

ABI minor 1 now makes resource allocate/release and completion release
mandatory. Host unload is busy while calls, sessions, resources, or completions
remain live. `std.gpu.provider` supplies the previously missing pure-Simple
typed facade and rejects invalid/cross-session handles and malformed receipts.
The native boundary now independently tracks each owned handle and rejects
cross-session wait/readback/release; closing a session with live children is
busy. Per-handle leases make concurrent completion release during wait and
resource release during readback return busy; a deterministic atomic-handshake
fixture passed both races with subsequent successful release/close/unload.
The same focused harness passes AddressSanitizer and UndefinedBehaviorSanitizer
with leak detection enabled.
An ASan/UBSan path-lifetime harness also proves the thread-local provider-path
snapshot remains readable and exact after unload. A focused bounded-path harness
proves a 4,096-byte configured path fails closed.
Duplicate live handles and corrupted receipt identity
or correlation also fail closed. This prevents raw extern callers from bypassing
facade ownership checks.
The updated checker source exercises all ownership classes, but the provider
checker was not rerun because its mandated three-cycle cap was already reached;
C syntax, shell syntax, and scoped diff checks pass.

## Fresh CUDA profile

The physical CUDA `FillU32` gate passed exact device readback with zero
mismatches on an NVIDIA RTX A6000. Tier 3 correctly kept all measured batches
CPU-selected. At 1,048,576 elements the median was 7,527 us GPU versus 3,236 us
CPU; allocation, readback, and conversion dominated. The production CUDA
executor now retains device, host, and argument buffers across warm calls. A
source-matched Stage4 probe remains required to measure that implementation
change; the direct C evidence does not promote it.

## CUDA DB filter implementation

A shared data-bearing inclusive `u32` filter IR now has an independent CPU
oracle and a CUDA PTX executor with cached input/output buffers. Its production
adapter passes the exact device receipt into DB admission and accounts for the
batch once; the previous two-submit device adapter defect was removed.

Modern unit and physical integration SSpecs cover invalid IR/masks, exact
mask and row projection, repeated warm dispatch, receipt validity, the 4 KiB
admission threshold, and queue completion. They remain **BLOCKED**, not PASS:
the apparent release executable reports that it is the Rust bootstrap seed,
and repository policy forbids using it instead of a pure-Simple Stage4 runner.
The DB executor now also exposes the canonical unavailable/init/submit/readback/
mismatch fault phases. Its live recovery scenario requires an injected
readback failure to return no handle or pixels, then exact recovery using the
same cached executor and stable device identity.

CUDA DB admission now validates IR and performs the exact queue, target,
generation, and budget preflight before CUDA initialization or allocation.
Rejected batches therefore incur no device setup, upload, or kernel launch.
New scenarios cover full `u32` extrema, a 257-row partial block, 4,096 patterned
rows, a below-threshold batch, and a malformed above-threshold batch.

## Fresh CUDA rendering

`check-cuda-generated-2d-readback.shs` passed on two detected CUDA devices.
The generated PTX artifact executed fill, copy, alpha, and scroll operations;
all 64 returned pixels matched the independent oracle with zero mismatches and
no blur or tolerance. This proves physical CUDA rendering, while the broader
Simple Engine2D SSpecs still await the pure-Simple runner.

## Web/DB timing hardening

Production promotion now requires both a positive device duration and a real
ordered host interval (`started_us > 0`, `finished_us > started_us`). Exact
readback alone can no longer promote fabricated zero timestamps. Modern SSpecs
cover missing host timing and missing device duration with typed reasons.

The existing CUDA WebIR/layout executor now retains its real handle, device
identity, readback source, exact geometry checksums, mismatch count, and
device-lane duration in `LayoutExecutionProof`. A new server bridge converts
only complete `hybrid_vector_gpu` proofs into strict device receipts and then
still requires exact HTTP status/body parity. Physical WebIR SSpec execution
awaits Stage4; this source work is not reported as a native PASS.
The web CUDA port now replaces four device and six host allocations per call
with one bounded device arena and one aligned host arena. Physical SSpecs assert
the one/one allocation counts plus transfer and arena sizes. A 64-cycle lifecycle
scenario additionally requires exact checksum parity, zero mismatches, and stable
device identity on every iteration. Execution and measurement remain pending
Stage4 and therefore have no fabricated PASS or speedup claim.
The production render session also previously recreated its CUDA context/module
for each layout and supplied an empty oracle, which prevented qualification.
It now retains one CUDA port, refreshes the snapshot oracle before dispatch,
reuses warm context/module handles and bounded device/host arenas, and closes
the port with the session. Warm evidence requires zero new arena allocations.
The retained-port recovery audit found that activation or module-load failure
could shut down a context while leaving its cached device pointer populated.
Both failure paths now release/clear the arena before shutdown, preventing a
later context from reusing foreign device memory. A unit SSpec locks the
initialization, execution-failure, and successful-warm cleanup branches.

## Metal native row

The generated Metal 2D checker failed closed with
`trusted-artifact-admission-failed`: this Linux host has no Metal runtime,
`metal`, `metallib`, admitted manifest, submission, or readback. The macOS
fill/copy/alpha/scroll row remains open.

## Fresh Vulkan physical row

The strict C11 Vulkan benchmark now declares its POSIX timing surface and
compiles with `-Wall -Wextra -Werror`. On the physical RTX A6000, a 3,840 x
2,160 fill over 31 samples returned exact readback (`0` mismatches), with
10.105 ms p50 and 10.280 ms p95 submit/fence time. The 80-fps submit budget
passes, but CPU and round-trip comparisons reject offload. No swapchain or
dynamic-frame result is claimed.

The 8K Engine2D native rows were then separated from their default llvmpipe
baseline and run on the physical RTX A6000. Clear was exact at 1.035 ms p95;
the retained mixed clear/rect/image/font frame was exact at 1.611 ms p95. The
old per-glyph font lane was exact but regressed to 41.408 ms p95. Selecting the
packed single-upload/single-dispatch lane reduced font p95 to 1.330 ms, so it
is now the default. All three checkers can require a discrete/integrated
adapter and the 80-fps budget; a new SSpec protects those fail-closed gates.

The Xvfb window-swapchain functional row reached the physical RTX A6000 with
dynamic one-percent damage, known completion, no fallback/readback, and a
nonzero checksum. It measured 80.360 ms p95 and therefore is not 8K80 evidence;
the physical-display row is BLOCKED because no reachable EDID-backed 8K80 mode
exists. This run also exposed and fixed Cargo-prefixed receipt parsing, which
previously exited silently. The checker now normalizes exactly one row, reports
malformed evidence explicitly, and self-tests both acceptance and rejection.
