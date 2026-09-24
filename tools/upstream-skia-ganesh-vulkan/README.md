# Optional upstream Skia Ganesh Vulkan provider

This directory is an explicit opt-in provider for the authenticated GPU
provider ABI v1 (`src/runtime/simple_gpu_provider_abi_v1.h`). No default
embedded build imports or links this directory. The backend ID presented to
the drawing layer is `upstream-skia-ganesh-vulkan`; the dynamic ABI backend bit
remains `SIMPLE_GPU_BACKEND_VULKAN`.

The immutable source revision is recorded in `skia-pin.json`. A builder must
check out that exact Skia commit, sync its pinned dependencies, enable Ganesh
and Vulkan, and record the checkout and dependency receipt. Skia's public
Vulkan example documents `GrDirectContexts::MakeVulkan`, an offscreen
`SkSurfaces::RenderTarget`, flush, submit, and the required destruction order:
<https://skia.googlesource.com/skia/+/35d5edfa0d50984c22ff94f5438c31e0db12c6f8/example/VulkanBasic.cpp>.

The private drawing payload v1 supports only opaque filled source-over
rectangles within the surface, starting with an integer full-surface clear.
The separate private v2 payload retains that clear and adds an optional
target-coordinate integer clip to each subsequent rectangle. Each clip is
validated before submission and scoped with `save`/`restore` around one draw;
an empty clip produces no pixels. V1 remains the format for scenes without
clips. Translation, styled boxes, text, images, and effects remain unsupported
until their semantics have dedicated payload operations.
The Simple adapter checks the complete `DrawIrComposition` before opening a
session. Later fractional `f64` bounds pass unchanged only when each value is
exactly representable by Ganesh's `f32` SkScalar. The native provider repeats
the payload checks before recording work. Its session owns the Vulkan
instance, physical and logical device, graphics queue, Ganesh context, surfaces,
completions, and resources. Every operation is thread-affine. A completion is
admitted only after flush, submit, GPU completion, and readback succeed. Device
loss poisons rendering on the session. Close still requires all child resources
and completions to be retired; after a lost-device idle result it releases
Ganesh resources while Vulkan handles remain live and then destroys the device.
The authenticated loader must retain uncertain work until close can safely
retire those children.
Both ABI layers cap an offscreen surface at 16,777,216 pixels and require a
nonzero submission correlation token.
The Ganesh render target and RGBA readback explicitly use sRGB color space;
rectangle rasterization disables antialiasing. Exact pixel parity with the
fractional Vulkan rectangle lane still requires physical-device evidence.
The v2 clip transport has only static header checks in this workspace; it has
not been compiled against the pinned Skia checkout or run on a GPU.

## Private v3 affine contract (default disabled)

The proposed v3 format is `0x33564b53` with magic `0x334b5355`. Its 128-byte
rectangle retains the exact v2 64-byte prefix and appends six `f64` affine
coefficients at byte 64, raster policy at byte 112 (`0` aliased pixel center,
`1` coverage AA), and zero reserved bytes through byte 127. Flag bit 1 marks
an affine transform; flag bit 0 retains the surface-coordinate clip. When
affine is absent, all six coefficients are zero. The first full-target clear
is opaque, untransformed, unclipped, and aliased.

The native CPU-only shape validator rejects nonfinite, noninvertible,
unsupported, or reserved values. For affine rectangles, source `f64` local
bounds and matrix coefficients may be converted to SkScalar only when the
submitted `f32` matrix stays finite and invertible and every transformed corner
has a conservative error of at most **0.125 physical pixels**. The error
includes a float arithmetic guard. This bound is a predeclared design policy,
not verified physical pixel equivalence. A future admitted v3 receipt must
record the original six `f64` coefficients, six submitted `f32` coefficients,
and maximum measured corner error. Native execution must save canvas state,
apply the surface clip before the affine transform, set the requested coverage
AA, draw, restore, and complete GPU readback before admitting pixels. The
experimental native implementation now follows that sequence. It uses a full
target `SkCanvas::clear` for the first command and the existing synchronous
flush, submit, device-idle, and readback tail for the scene.

`SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3` is a compile-time C++ macro with value
`0` by default. Default native builds reject v3 after complete CPU validation
and before creating GPU work. Set
`SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3=1` when running `build-linux.shs` (or
`build-macos.shs` on macOS) to
build the experimental native v3 path; its receipt records that selection.
The Simple adapter exposes a separate candidate entrypoint, while its default
entrypoint remains v1/v2 only. No pinned-Skia compilation or physical Linux
Vulkan run has validated the enabled path, and the ABI receipt does not yet
carry submitted-matrix provenance. V1 and v2 payload bytes and exact SkScalar
rules remain unchanged.

The Simple `upstream_skia_ganesh_vulkan_final_capture` adapter checks the
returned byte count and native FNV checksum, then records the readback's RGBA,
straight-alpha, sRGB, top-left domain. It supplies no independent physical
device identity; a caller-constructed frame cannot qualify N2.

`SIMPLE_VULKAN_PROVIDER_PATH` and `SIMPLE_VULKAN_PROVIDER_SHA256` select and
authenticate the optional shared object. Since the runtime has one Vulkan
provider slot, selecting this provider replaces any other Vulkan provider for
that process. Cross-backend comparison therefore uses separate authenticated
process runs with the same pinned scene and fixture digest. The ABI receipt's
`device_identity` is the chosen device index; the qualification runner must
independently record `VkPhysicalDeviceProperties` (vendor, device, driver, API)
and the physical Linux host. The build helper forces the pinned `DEPS` into
Skia's synchronizer, verifies every enabled Git dependency checkout against
its pinned revision and clean worktree before and after building, and records
the checkout manifest and digest alongside archive/provider hashes. CIPD
packages remain identified by the pinned `DEPS` hash. No claim of native
build, device support, or pixel equivalence is made
by a header syntax check or by the pin receipt alone.

`submit()` remains synchronous: it waits for Skia submission, device idle, and
readback before returning a completion handle. The adapter's five-second
`wait()` timeout starts only afterward and does not bound a blocked `submit()`
or Vulkan driver call. The receipt field `device_elapsed_ns` currently records
host steady-clock time from surface creation through readback, including CPU
work and waits; it is not a GPU timestamp or device-only duration.

## Controlled rectangle physical qualification

On a physical Linux Vulkan host, from the repository root, use a clean Skia
checkout at the pinned revision and build the optional provider and native
qualification executable:

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

Use the matching self-hosted release compiler on another Linux architecture.
The build helper writes a `<provider>.receipt.json` with the pinned Skia
revision, verified Git dependency revisions and hashes, GN arguments and
provider SHA-256. The runner reads up to 32 KiB, requires a nonempty checkout
manifest and its digest, and hashes the complete receipt. It runs Engine2D and Skia in separate
bounded workers with explicit provider choices. Engine2D's Vulkan provider is
linked into the qualification executable, so its provider SHA-256 equals the
executable SHA-256; Skia uses the separate shared-object SHA-256.

The retained `<backend>.rgba` files contain canonical, tightly packed
16 × 16 top-left RGBA8 pixels. Their receipts preserve the native capture's
pixel layout in `source_*` fields and describe the canonical file layout
separately. `run.sdn` and `comparison.sdn` record the fresh run and exact
pixel/oracle verdict. The CLI's `verify` subcommand accepts existing artifacts
only as `candidate`; it never issues physical PASS. See
`doc/03_plan/sys_test/physical_vulkan_2d_controlled_rectangle.md` for the full
contract and artifact list.

Status (2026-09-26): **blocked**. This macOS workspace has neither the pinned
Skia checkout nor a physical Linux Vulkan readback. The qualification source
has not compiled here because the self-hosted check fails earlier in unrelated
`src/lib/nogc_sync_mut/io/process_ops.spl` parsing. No physical PASS is claimed.

Status (2026-09-27): macOS prerequisites verified (Vulkan loader
`/opt/homebrew/lib/libvulkan.dylib`, MoltenVK 1.4.1 ICD, ninja, clang++, and
the in-checkout `bin/gn` are all present), and a deterministic
`build-macos.shs` helper now mirrors `build-linux.shs`: same pin/DEPS/clean
worktree gates and dependency checkout manifest, Darwin link closure
(`-dynamiclib`, `-Wl,-undefined,error`, CoreFoundation/CoreGraphics/CoreText/
Accelerate frameworks, Vulkan loader only — MoltenVK is recorded in the receipt
as a runtime ICD, never linked), and a receipt that additionally binds the
loader and MoltenVK library digests. The helper exits 2 without `SKIA_ROOT`;
its full build is untested because the pinned Skia checkout is still absent.
A Mac MoltenVK provider build remains backend evidence only — it cannot
satisfy NFR-2D-002's physical Linux Vulkan requirement.

Status (2026-09-27, night): both provider variants built on the pinned
checkout; device probes passed on the admitted MoltenVK device (see
`build-status.md`).

## macOS device probes: MoltenVK is the Vulkan backend

MoltenVK is the only admissible macOS Vulkan backend for this lane. Every
device probe, scene probe, and fault-injection run on macOS must execute with
the canonical Homebrew MoltenVK ICD pinned:

```sh
. "$(dirname "$0")/env-moltenvk.shs"   # exports VK_ICD_FILENAMES, digest-pinned
```

`env-moltenvk.shs` resolves `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`,
verifies the ICD and `libMoltenVK.dylib` SHA-256 digests against the stage-2
device preflight receipt
(`build/tmp/macos_vulkan_2d_preflight_2026-09-27/preflight.env`, MoltenVK
1.4.1), and fails closed on drift. Device evidence produced under any other
ICD — or with the digests drifted — is rejected by
`scripts/check/check-macos-gpu-2d-live-evidence.shs`, which applies the same
canonical-ICD pin to the full live harness.
