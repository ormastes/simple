# CUDA bitmap AND provider v1

## Scope and admission

This Linux extension implements the existing `simple_gpu_provider_abi_v1`
CUDA lifecycle. It is an optional foreign device boundary, not a replacement
for Simple database, web, compiler, or vector algorithms. Base revision:
`eff05db338d813ca93a39cfdd9b23dde988d90b1`.

The host registry authenticates the shared object's real SHA-256 through
`SIMPLE_CUDA_PROVIDER_PATH` and `SIMPLE_CUDA_PROVIDER_SHA256`, snapshots it,
and admits its ABI. Query and format discovery are immutable and inert: they
do not load libcuda, initialize a device, or create a context. Only an admitted
session operation loads the CUDA Driver API. Provider identity is
`0x43554441414e4431`; receipt device identity is the host-selected CUDA ordinal.
The GPU UUID is external evidence, not an invented receipt field. The current
registry exposes **no device-image attestation**; its authority query stays 0.

Production owner: `src/runtime/providers/cuda/bitmap_provider_v1.c`.
The PTX is byte-identical to the previously executed bounded Driver API proof,
using PTX 6.0 / sm_61 and 128 threads per block with a count guard. The audio
driver shim informed symbol/prototype selection but is not linked: audio
operations and its unchecked context destruction are not part of this provider.

## Format and ownership

Submission format 1 is little endian: u32 word count, u32 reserved zero,
`count` left u32 values, then `count` right u32 values. The only operation is
word-wise AND. Count must be 1..16384, total length exactly `8 + count*8`,
and resource size exactly `count*4`. Resource flags are 0 and usage bits 1.
All size arithmetic follows the count bound; output is at most 65536 bytes.
An empty bitmap is rejected before work. A future Simple caller must return
the correct empty result without submitting; this package does not yet wire
that caller. Operation-table entry 0 discovers supported format 1.

Capacity is one session, one resource and one completion. Creation beyond
capacity returns REJECTED with no new object, avoiding false host quarantine.
Handles monotonically increase to INT64_MAX, then permanently exhaust during
the loaded library lifetime. The canonical host registry supplies the unload
generation; provider tokens are never exported as interchangeable host tokens.

A mutex serializes provider state. Each device callback pushes its context
and pops it before returning; the caller's thread-local context is preserved.
Creation's initially current context is popped too. Submission copies both
borrowed arrays into owned host storage before upload; the provider retains
no caller pointer. Device allocations, events and host buffers have explicit
owners. Wait polls an actual completion event with a monotonic deadline,
reads actual event time, downloads output, and computes FNV-1a-64. Readback
copies the completed bytes; the host independently verifies the checksum.

Completion release synchronizes before destroying any potentially in-flight
storage. A failed drain retains all resources. Partial cleanup clears only
successfully destroyed objects, permitting safe retry. Failed context pop
permanently quarantines that session because its stack cannot be trusted.
Context destruction errors retain the session; shutdown refuses live state.
No destructor silently releases active device storage. A fatal device/context
error can therefore require process retirement rather than unsafe unload.

If `cuCtxCreate` fails but returns a non-NULL context, open returns UNCERTAIN
with its retained handle. The registry attempts the same checked close and
otherwise quarantines it. Caller-stack restoration in that rare creation-error
case is not established by the successful-call tests; there is no blanket
failure-path context guarantee.

## Executed evidence, 2026-10-05

Hardware: WSL Linux, NVIDIA Quadro P4000, compute capability 6.1, Windows
driver 582.78, UUID `GPU-c44a4537-6124-77b1-e956-28f2cb13d734`.
Host compiler: Clang 23.1.1. No CUDA SDK, nvcc or driver installation was needed.

The actual production host registry (`runtime_dynload.c` + `runtime_native.c`)
loaded the real provider by its actual artifact digest. The integration harness
passed eight device launches at counts 1,31,32,33,127,128,129,1025: 1506 words,
independent arithmetic scalar oracle, high bits, 128 host output canaries,
copied-input lifetime, duplicate/stale handle rejection, retained unload,
resource retirement, and caller/worker-thread context preservation. Invalid
format, length, empty and oversized requests were rejected. A separate process
rejected a wrong artifact digest while libcuda remained unloaded. An admitted
metadata query also left libcuda unloaded. Real event time totaled 2399801 ns;
this is completion evidence, **not a performance comparison**.

Retained output: `/var/tmp/item5-cuda-registry-proof-20261005/` contains
`run.log`, `denied.log`, `run.rss.env`, `status.txt`, `compile.log`,
`source.sha256`, `artifacts.sha256`, and binaries. Exit 0; enforced 1000000 KiB
host RSS / 60 second execution budget, peak 137320 KiB. This bounds host RSS,
not VRAM (device buffers are separately bounded by the format).

| Artifact | SHA-256 |
|---|---|
| Provider source | `fc58672a738ff74fbfc7a533c8723606db99a53117cae908b49c4d9bec2ff60c` |
| Native registry test source | `e5445ceb3096989e64501fa983fd9d9f6d53460ea599506273fd6f887d1fb83e` |
| Provider shared object | `b9bd227520ba39664fccc675320e29dd575d6999c85c5ca467a87541f2cac65c` |
| Native registry test executable | `4afdb4852af8a084060eb42b595b95c31c376e1926fc1fdb0b5cce8215550c73` |
| Failure-policy test source | `d540b28ff551c76d68be8c3a6e4547d3e4c8b6fb4dbdcb626f00dcd276238b4d` |
| Failure-policy executable | `489ae773fa86c736ded16dcfd11756419ec43495be976a5e2f333c044826368d` |

The separately executed failure-policy selfcheck includes the actual provider
source and replaces Driver API function pointers with deterministic failures.
It passed permanent exhaustion, timeout retention, failed-drain quarantine,
successful recovery, destroy failure retention, and context-failure quarantine.
`failure.log` records PASS. These are mocked failure-policy tests, not device
execution. Actual hardware fault injection and all Driver API failure sites
are not qualified by that test.

## Reproduction and remaining integration

On a Linux CUDA host, using a new output directory:

```sh
CC=clang sh scripts/check/check-cuda-bitmap-provider-v1.shs /absolute/new/output
```

On WSL, add `/usr/lib/wsl/lib` to LD_LIBRARY_PATH when needed. Unsupported host
or unavailable CUDA is exit 77, never PASS. Driver absence is checked after
the inert admission test. Compilation failures and device failures stay failures.
The wrapper was extended after the hardware PASS to include the separately
passed failure-policy selfcheck; shell syntax was checked without repeating
the unchanged green hardware criterion.

A separate maximum-only invocation subsequently passed **one 16384-word
device launch**, 16 output canaries, and rejection of count 16385 plus
UINT32_MAX count with INT64_MAX wire length. The previous eight-launch receipt
was preserved, not rerun. Retained outputs are
`/var/tmp/item5-cuda-registry-maximum-20261005/` (`run.log`, `status.txt`,
`run.rss.env`, `artifacts.sha256`). The production provider bytes stayed
identical; the harness gained the bounded `--maximum-only` mode. Its revised
hash is recorded in that separate receipt. The wrapper accepts the same mode
as its second argument. Reproduce both criteria in separate fresh output
directories. Zero-word rejection does not qualify a Simple empty-result path.

No Simple DB/web application, dynload Simple facade, vector planner dispatch,
benchmark, Windows DLL, other GPU, or device-image attestation is qualified.
The next integration needs a bounded Simple format-1 encoder with an explicit
empty-result path and the existing admission/session/receipt owners. This
hardware-specific check is registered in `scripts/check/guard_wiring_optout.txt`
as explicit/manual, not a generic CI gate.
Parent/root owns final source review and landing; no release admission is
claimed by these component results alone.
