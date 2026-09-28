# Physical Vulkan 2D controlled rectangle qualification

This is a focused prerequisite slice for REQ-2D-003, REQ-2D-005 and REQ-2D-006. The source is `test/fixtures/simple_2d_skia/controlled_opaque_rect_v1.sdn`; the qualification contract recomputes its SHA-256 from that file. The scene is a 16 × 16 opaque clear and an opaque integer rectangle. It does not cover fractional geometry, Web layout, GUI widget state, or the 48-case HTML/CSS corpus.

The same isolated runner now also has a separate `run-clip` lane for the
pinned clipped rectangle scene. Its scope and open physical evidence are in
`physical_vulkan_2d_controlled_clip.md`; a rectangle-only result cannot count
as clipped-pixel evidence.

The two backend capture adapters must run with their own authenticated Vulkan provider processes. Each adapter must return completed physical-device submission, fence, device-origin readback, device name/type/driver, and a `FinalOutputCapture` whose resource identity, subresource, dimensions, stride, format, alpha, color, origin, crop, and submission/completion tokens come from the backend or capture tool. The pair contract rejects software Vulkan, fallback, degraded producer output, missing pixels, and missing metadata before calling `compare_final_output_pixels` with exact tolerance.
The paired runs must report the same physical device type, Vulkan
`deviceUUID`, and Vulkan `driverUUID`; a mismatch blocks the comparison.
Device names and formatted driver strings are retained as diagnostics because
the two backends can format the same native properties differently. Each UUID
is 16 bytes encoded as 32 lowercase hex digits, and an
all-zero or malformed value blocks admission. Engine2D's
`rt_vulkan_get_device()` now returns a monotonic selected-device generation
token, while the Skia provider records a device enumeration index. Neither is
a cross-process physical identity, so those numbers cannot be compared. Each
owner queries `VkPhysicalDeviceIDProperties` from its *selected* physical
device and binds the returned UUIDs to its completed capture receipt.
Khronos specifies `deviceUUID` for cross-process device correlation:
https://docs.vulkan.org/refpages/latest/refpages/source/VkPhysicalDeviceIDProperties.html

Current qualification status: **blocked** (2026-09-26). Both in-process adapters can
construct `FinalOutputCapture`, and both now have owner-scoped native UUID
query paths. Their deployment and live physical GPU behavior remain
unverified. The shared provider slot also requires separate processes for the
two backends. A numeric backend handle or caller-constructed result cannot
establish physical-device provenance.
The pair contract now rejects missing or unequal reported UUIDs, but its
`candidate` verdict still does not authenticate their origin.
The Skia side has a checked frame-to-`FinalOutputCapture` conversion with
code-owned pixel-domain metadata and checksum verification. The optional
native provider identity export is tied to its selected session and completed
readback; the conversion alone cannot authenticate a caller-constructed frame.
The Engine2D strict path now links readback to the same completed Vulkan fence
generation and framebuffer handle, then converts checked packed ARGB words to
RGBA bytes. Both adapters are still caller-visible data paths, so their output
remains a structural candidate until native session provenance is recorded.

Execute the native provenance adapters in separate processes on a prepared Linux host with discrete or integrated Vulkan hardware. Retain their canonical RGBA files, source-capture metadata, and device/driver receipts, then run the controlled pair and oracle checks. Any unavailable backend or device remains `blocked`; a pixel difference or a common-mode difference from the independently rasterized pinned rectangle is `fail`. Exact oracle-matching caller-supplied bytes yield `candidate` until the controlled runner independently authenticates fresh physical-device and source provenance. This rectangle result cannot be promoted to Web/GUI corpus coverage.

## Physical runner contract

`src/app/test/vulkan_2d_qualification/main.spl` owns `run`,
`worker-engine2d`, `worker-skia`, and `verify` commands. `run` launches the
backend workers in separate processes with explicit provider paths, the pinned
fixture, a new output directory, bounded execution, and a fresh run ID.
Workers produce their own completed `FinalOutputCapture`, selected-device
UUIDs, raw RGBA file, and machine-readable receipt after successful
readback and owner retirement. They never load another backend's provider.

The orchestrator independently hashes the fixture, executable, linked
Engine2D provider identity (the same executable SHA-256), optional Skia shared
object and its pinned build receipt, and returned canonical pixels; checks
worker exit status, run/backend IDs,
artifact paths and lengths; then compares both canonical outputs exactly
against each other and against the analytic 16 × 16 rectangle oracle. The
oracle pins expected geometry, colors, and RGBA SHA-256 independently of the
fixture-to-DrawIR parser; the fixture SHA-256 binds that expected image. A
matching caller-constructed pair stays `candidate`. Only a receipt produced
by this controlled worker execution may become `PASS:
controlled-rectangle-only`. Native host/worker compromise is outside this
local proof; remote admission needs trusted runner identity and signed run
metadata. Web and GUI remain separate open scene matrices.

## Linux execution and retained evidence

From the repository root on a physical Linux Vulkan host, with a clean Skia
checkout at revision `35d5edfa0d50984c22ff94f5438c31e0db12c6f8`:

```sh
export SKIA_ROOT=/absolute/path/to/pinned/skia
sh tools/upstream-skia-ganesh-vulkan/build-linux.shs \
  "$PWD/build/optional/libsimple_upstream_skia_ganesh_vulkan.so"
bin/release/x86_64-unknown-linux-gnu/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/test/vulkan_2d_qualification/main.spl \
  --strip --output build/optional/vulkan_2d_qualification
"$PWD/build/optional/vulkan_2d_qualification" run \
  "$PWD/build/optional/vulkan_2d_qualification" \
  "$PWD/build/optional/libsimple_upstream_skia_ganesh_vulkan.so" \
  build/test-artifacts/vulkan_2d/controlled_rect_001
```

Use the corresponding self-hosted release binary on another Linux CPU
architecture. The output directory must be a fresh single-segment child of
`build/test-artifacts/vulkan_2d/`; `run` refuses an existing directory. The
native executable must execute itself: `run` and each worker compare its file
hash with `/proc/self/exe`. The orchestrator clears the optional provider
selection for the Engine2D worker and selects the pinned Skia provider only in
the separate Skia worker. Each worker has a 120-second process bound and a
64-KiB output bound.

Each worker writes `<backend>.rgba` and `<backend>.sdn`. The `.rgba` file is
canonical, tightly packed 16 × 16 top-left `R8G8B8A8_UNORM` with straight
alpha, 64-byte stride and 1024 bytes. The receipt records those file-domain
fields and separately records the source capture's stride, pixel format,
alpha, origin and crop under `source_*`. The saved bytes may therefore differ
in layout from the native readback while representing the same pixels.
Completed submission/readback tokens, selected resource, device status,
physical device and driver UUIDs, provider provenance, SHA-256 hashes, and the
fresh run nonce remain in the receipts. `run` retains bounded worker logs,
`comparison.sdn`, and `run.sdn`; `run.sdn` is written last after exact pair and
independent analytic-oracle checks. Its `status: pass` is scoped solely to the
controlled rectangle.

For offline inspection, `verify <output-dir> <executable-sha256>
<skia-provider-sha256>` checks candidate files and returns `status=candidate`
with exit 3 even when their pixels match. Imported receipts cannot prove fresh
worker exits and cannot be promoted to physical PASS. No compiled CLI run or
physical Linux PASS has been observed in this workspace. The attempted
self-hosted check was blocked before this source compiled by the unrelated
`src/lib/nogc_sync_mut/io/process_ops.spl` parser error; native build and
device qualification remain required.
