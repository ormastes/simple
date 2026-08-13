# Engine2D Vulkan Clear 8K Evidence — 2026-08-12

Status: **FAIL full-frame 8K/80; PASS retained compute evidence**

This gate links directly to the Vulkan-enabled `simple-runtime` ABI and follows
the Engine2D clear lifecycle: 132,710,400-byte storage buffer, 256-thread clear
compute SPIR-V, 64-byte push constants, descriptor binding, command recording,
dispatch, fenced submission/wait, and dependency cleanup. Timing excludes
readback. A separate exact readback verifies zero mismatches and checksum
`11192757161153971075` for the full 8K frame.

Pinned llvmpipe measurements (15 samples):

| Active pixels | p50 ns | p95 ns | Isolated 12.5 ms budget |
|---:|---:|---:|---:|
| 5% | 1,099,999 | 1,545,870 | PASS |
| 25% | 5,275,748 | 6,906,621 | PASS |
| 50% | 8,862,893 | 12,218,878 | PASS |
| 75% | 19,708,381 | 23,437,297 | FAIL |
| 100% (canonical wrapper) | 22,629,394 | 25,944,270 | FAIL |

The conservative isolated retained envelope is 50% on this software Vulkan
device. This is a real Engine2D-compatible compute dispatch, but not a complete
DrawIR frame: there is no traversal, multiple primitives, presentation owner,
swapchain, or scanout. llvmpipe is CPU Vulkan, not physical-GPU evidence. The
receipt therefore reports zero timed readback bytes while keeping
`swapchain_presented=false` and `dynamic_frame_80fps_proven=false`.

Reproduce with `scripts/check/check-engine2d-vulkan-clear-8k.shs`; set
`ENGINE2D_VULKAN_ACTIVE_BASIS_POINTS` for retained sweeps and
`VK_ICD_FILENAMES` for an explicitly selected device ICD.

## 2026-08-13 physical-GPU retained clear receipt

The primitive benchmark receipt now records the selected adapter name, type,
driver identity, and stable identity hash. This prevents an ICD selection from
being reported as hardware evidence without identifying the device that the
runtime actually chose. The following 15-sample run used the NVIDIA ICD:

```sh
BUILD_DIR=build/check/engine2d-vulkan-clear-8k-nvidia-active1-attributed-20260813 \
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json \
ENGINE2D_VULKAN_ACTIVE_BASIS_POINTS=100 ENGINE2D_VULKAN_SAMPLES=15 \
sh scripts/check/check-engine2d-vulkan-clear-8k.shs
```

| Adapter | Type | Active pixels | p50 ns | p95 ns | Timed readback | Oracle | Result |
|---|---|---:|---:|---:|---:|---|---|
| NVIDIA RTX A6000 | discrete | 331,776 (1%) | 608,384 | 670,132 | 0 bytes | 0 mismatches; checksum `9960456387733476227` | isolated PASS |

The recorded driver identity was
`NVIDIA RTX A6000|vendor=000010de|device=00002230|driver=911f8400|api=00404138`
(hash `666008366`). The evidence readback after timing was 1,327,104 bytes and
is solely the exact oracle for the changed region. The receipt still says
`swapchain_presented=false` and
`engine2d_vulkan_dynamic_frame_80fps_proven=false`: this proves only an
isolated retained clear compute submission on a physical adapter, not DrawIR
traversal, mixed rendering, device presentation, scanout, or end-to-end 8K/80.

## 2026-08-13 physical-GPU mixed retained batch receipt

The mixed Engine2D baseline now records selected-adapter provenance and a
full-buffer FNV checksum as well as its exact oracle mismatch count. It creates
the 8K retained framebuffer once, then each timed frame records a 100-pixel
solid strip, 16 one-pixel axis-aligned lines, a stable 50-pixel-high image
copy, and 1,024 packed 16×16 atlas glyphs into one command buffer and waits one
fence. The post-timing readback is the entire framebuffer and is not charged to
the timing interval.

```sh
BUILD_DIR=build/check/engine2d-vulkan-mixed-8k-nvidia-attributed-20260813 \
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json \
ENGINE2D_VULKAN_SAMPLES=31 ENGINE2D_VULKAN_GLYPHS=1024 \
ENGINE2D_VULKAN_LINES=16 \
sh scripts/check/check-engine2d-vulkan-mixed-8k.shs
```

| Adapter | Workload | Dispatches / submissions | Changed pixels | p50 ns | p95 ns | Oracle |
|---|---|---:|---:|---:|---:|---|
| NVIDIA RTX A6000 (discrete) | retained fills, lines, image, packed text | 19 / 1 | 1,537,024 | 1,434,555 | 1,463,700 | 0 mismatches; checksum `11020250275472069507` |

The adapter identity was
`NVIDIA RTX A6000|vendor=000010de|device=00002230|driver=911f8400|api=00404138`
(hash `666008366`). The row fits the isolated 12.5 ms GPU compute/fence budget
and has zero timed readback bytes. Its 132,710,400-byte evidence readback,
full-frame framebuffer seed, DrawIR traversal, resource upload, swapchain
presentation, and scanout are excluded or absent. The receipt deliberately
retains `swapchain_presented=false` and
`engine2d_vulkan_mixed_dynamic_frame_80fps_proven=false`; it must not be read
as a complete GPU/DrawIR/Web/GUI/WM 8K/80 result.

## Batched filled rectangles and barrier correction

The representative DrawIR-style batch seeds a retained 8K framebuffer, records
multiple non-overlapping filled-rectangle dispatches against one descriptor and
one command buffer, then performs one fenced submission. A full evidence
readback checks both the 5% changed prefix and the untouched retained pixels.

Initial evidence exposed a runtime synchronization defect: every dispatch
inserted a COMPUTE→HOST barrier even though the next consumers are other
compute dispatches or a transfer-stage evidence copy. Replacing HOST with
COMPUTE|TRANSFER and SHADER_READ|SHADER_WRITE|TRANSFER_READ preserves exact
parity while removing premature host visibility from the hot batch.

At 5% damage on llvmpipe:

| Rectangles | Before p95 ns | Corrected p50 ns | Corrected p95 ns | Budget |
|---:|---:|---:|---:|---:|
| 1 | 21,043,726 | 1,850,862 | 2,359,713 | PASS |
| 16 | 29,421,072 | 3,763,351 | 4,483,415 (31 samples) | PASS |
| 32 | 45,818,571 | 10,026,392 | 12,997,020 | FAIL |
| 48 | not measured | 10,957,790 | 13,186,953 | FAIL |
| 64 | 95,570,340 | 12,984,556 | 15,819,065 | FAIL |

The conservative isolated envelope is therefore 16 filled rectangles at 5%
damage on this software Vulkan device. These rows still exclude DrawIR traversal
and swapchain presentation and are not physical-GPU proof.

## Batched lines and the axis-aligned fast path

The ordered line shader preserves Bresenham semantics by walking an entire line
in one invocation. Exact full-buffer readback reported zero mismatches, but a
7680-pixel horizontal line is consequently serial inside the device invocation.

| Ordered full-width lines | p50 ns | p95 ns | Budget |
|---:|---:|---:|---:|
| 4 | 3,295,017 | 3,934,111 | PASS |
| 8 | 7,199,411 | 8,629,792 | PASS |
| 12 | 9,837,918 | 10,905,985 | PASS |
| 16 | 14,960,966 | 16,741,019 | FAIL |

Thickness-1 horizontal and vertical lines are exactly inclusive filled
rectangles. Engine2D now routes that common border/separator case through the
parallel rectangle pipeline while retaining the ordered oracle for diagonal and
thick lines. Reversed endpoints and inclusive endpoints are covered explicitly.

| Axis-aligned full-width lines | p50 ns | p95 ns | Budget |
|---:|---:|---:|---:|
| 16 | 3,337,894 | 4,082,089 | PASS |
| 32 | 6,597,206 | 8,837,706 | PASS |
| 48 | 10,405,449 | 11,976,258 | PASS |
| 64 | 13,200,004 | 15,473,279 | FAIL |

The conservative isolated envelope is 12 ordered lines or 48 axis-aligned
lines on llvmpipe. This remains compute-only evidence: it proves neither a
physical GPU nor swapchain presentation nor end-to-end dynamic 8K/80 rendering.

## Retained image copies and frame-owned source lifetime

The production image path previously flushed preceding primitives and issued a
separate fenced submission for every image. It now records image composites in
the Engine-owned frame command buffer. Each descriptor and uploaded source
buffer remains live until the shared fence completes, then the normal release
or quarantine owner disposes it. The fixed batch capacity flushes safely before
accepting a seventeenth unique image dependency.

The native ABI probe pre-uploads one opaque source, copies 5% of the retained
8K framebuffer, times only record/submit/fence completion, and performs an
untimed full-buffer oracle readback:

| Image regions | p50 ns | p95 ns | Mismatches | Budget |
|---:|---:|---:|---:|---:|
| 1 | 7,649,250 | 9,783,128 | 0 | PASS |
| 2 | 6,840,534 | 8,226,973 | 0 | PASS |
| 4 | 12,283,696 | 16,353,735 | 0 | FAIL |
| 8 | 10,745,798 | 15,498,321 | 0 | FAIL |
| 16 | 10,759,795 | 17,231,895 | 0 | FAIL |
| 32 | 15,268,782 | 17,531,196 | 0 | FAIL |

The conservative isolated llvmpipe envelope is two image regions at 5% damage.
Source allocation, CPU-to-device upload, DrawIR traversal, readback, and
presentation are excluded from the timed interval and must not be inferred as
8K/80 proof. Production still allocates/uploads each transient pixel array;
stable resource identities and a bounded device image cache remain required to
remove that cost for retained Web/GUI images.

## Warm pooled atlas text

The font atlas was already retained, but each production frame still allocated
one 52-byte parameter buffer and one descriptor per glyph. Batched text now
grows a bounded resource pool on demand and reuses those handles after the
shared frame fence. Parameter values and bindings are refreshed every draw;
unknown completion quarantines the entire pool before it can be reused.

The 8K native ABI probe uses the production atlas-composite semantics with
16x16 opaque glyphs. Its timed interval includes every per-glyph parameter
upload, command recording, one submission, and one fence, while excluding the
cold pool creation, atlas upload, and exact full-frame evidence readback.

| Warm glyphs | p50 ns | p95 ns | Mismatches | Budget |
|---:|---:|---:|---:|---:|
| 64 | 7,540,503 | 8,459,499 | 0 | PASS |
| 80 | 10,043,442 | 11,671,110 | 0 | PASS |
| 96 | 11,564,878 | 14,177,107 | 0 | FAIL |
| 128 | 17,135,018 | 19,842,961 | 0 | FAIL |
| 256 | 31,638,601 | 34,335,472 | 0 | FAIL |
| 512 | 65,617,711 | 80,649,691 | 0 | FAIL |

The conservative isolated llvmpipe envelope is 80 warm glyphs. This exposes
the next bottleneck cleanly: one staging upload and one dispatch per glyph.
Packing all glyph parameters into one buffer and dispatching a two-dimensional
glyph/pixel grid is required for dense Web text. This is not physical-GPU,
swapchain, mixed-DrawIR, or end-to-end 8K/80 proof.

## Packed atlas-text production cutover

The measured per-glyph upload/dispatch ceiling was architectural, not pixel
throughput. The pinned Vulkan font artifact now consumes one frame header plus
seven words per glyph from one storage buffer. A two-dimensional dispatch maps
X to pixels within the largest glyph and Y to glyph records. The production
owner uploads once, binds one descriptor, and records one dispatch per text
batch. Pool entries are frame-fence reusable and sized for the explicit
4,096-glyph cap; cumulative glyph accounting still rejects an oversized frame.

Exact 8K llvmpipe results for 16x16 glyphs, including the packed parameter
upload, command recording, submission, and fence:

| Packed glyphs | p50 ns | p95 ns | Mismatches | Budget |
|---:|---:|---:|---:|---:|
| 512 | 646,544 | 972,346 | 0 | PASS |
| 1,024 | 914,165 | 1,137,523 | 0 | PASS |
| 2,048 | 1,600,005 | 2,067,117 | 0 | PASS |
| 4,096 | 3,324,689 | 4,647,876 | 0 | PASS |

At 512 glyphs this reduces p95 from 80,649,691 ns to 972,346 ns (82.9x).
The pinned GLSL and embedded 7,012-byte SPIR-V hashes are checked against the
same source, and the full 132,710,400-byte framebuffer oracle reports exact
parity. Readback, DrawIR traversal, mixed primitives, and swapchain presentation
remain outside the timed interval, so this is a text-operation result rather
than an end-to-end 8K/80 claim.

## Mixed retained primitive envelope

The mixed native ABI probe records clear, solid fills, axis-aligned lines, one
stable pre-uploaded image, and packed atlas text into one command buffer and
waits one fence. Exact full-frame readback reports zero mismatches in every
row below. A deliberately fragmented 50-dispatch scene measured 59,386,000 ns
p95. Merging its 16 exactly adjacent solid fills reduced the scene to 19
dispatches and 12,758,000 ns p95, still just outside the 12.5 ms budget.

| Packed glyphs | Lines | Dispatches | p50 ns | p95 ns | Mismatches | Budget |
|---:|---:|---:|---:|---:|---:|---:|
| 1,024 | 12 | 15 | 6,542,000 | 8,051,000 | 0 | PASS |
| 1,024 | 16 | 19 | 9,577,000 | 12,758,000 | 0 | FAIL |
| 4,096 | 12 | 15 | — | 16,028,000 | 0 | FAIL |

Production DrawIR now performs the same exact fill reduction for consecutive,
unstyled, unclipped, same-colour rectangles that abut without overlap. It does
not reorder commands and retains logical command counts in executor receipts.

This is a conservative llvmpipe operation envelope, not an end-to-end 8K/80
claim. The timed interval excludes DrawIR traversal, source allocation/upload
for stable images, full-frame readback, and swapchain presentation. It also is
not physical-GPU evidence. The passing row establishes only that this retained
15-dispatch primitive mix fits the host software-Vulkan frame budget with an
exact post-timing oracle.

## Frame-receipt honesty gate

`VulkanBackend.latest_frame_receipt()` distinguishes `device-retained`,
`headless-swapchain`, `host-cache`, and `none`. A retained compute frame
records zero readback bytes but never claims presentation. The historical
`present()` call records its device-to-host byte count and cache-refresh result,
while `device_present` and `present_completed` remain false. Failed partial
readback preserves the dirty framebuffer and reports incomplete readback with a
specific reason; idle calls record no readback and no completed presentation.

The headless same-device bridge below closes that registry split for CI
presentation evidence. A visible window surface adapter remains tracked in
`doc/08_tracking/bug/engine2d_vulkan_swapchain_registry_split_2026-08-12.md`.

## Same-device headless swapchain presentation

The native runtime now supports an opt-in `VK_EXT_headless_surface` owner that
is created before physical/logical device selection. Engine2D compute storage,
swapchain acquisition, the fenced buffer-to-image transfer, and
`vkQueuePresentKHR` therefore share one device. The path performs no
device-to-host framebuffer transfer. A 64x32 llvmpipe live test completed two
successive presentations, exercising both first-use and retained image-layout
transitions.

At 7680x4320 on llvmpipe, 20 retained presentations measured p50 12,242,784 ns
and p95 12,611,891 ns, with peak RSS 579,696 KiB, zero readback bytes, known
completion, no CPU fallback, and source-buffer checksum
1055514150447629187. This is a narrow FAIL against 12.5 ms p95 by 111,891 ns.
The checksum proves the immutable presented source payload, not post-scanout
pixels; headless `vkQueuePresentKHR` completion is the presentation receipt.

The swapchain owner now tracks the content revision installed in each image.
After every image has been seeded, an unchanged retained frame is acquired and
re-presented without repeating the 132,710,400-byte device copy. With four
untimed seed presentations, the same 20-frame 8K probe measured p50 20,318 ns
and p95 30,117 ns, peak RSS 579,972 KiB, zero readback bytes, known completion,
no CPU fallback, and the same source checksum. This retained frame-switching
row passes the 12.5 ms budget, but it is explicitly cached replay: any changed
content revision seeds each acquired swapchain image again and remains governed
by the 12.612 ms dynamic-copy row above.

An earlier hardware-preferred NVIDIA headless probe terminated with SIGSEGV
while the pinned llvmpipe ICD passed. The headless evidence entry now prefers a
CPU ICD when one is enumerated, avoiding accidental hardware promotion. No
physical-GPU or visible-window promotion is claimed until that driver path is
diagnosed. The winit adapter below proves virtual-display correctness but is
not physical display evidence.

## Visible-window same-device correctness

The winit window surface now follows the same ordering as the headless owner:
surface creation, compatible device selection, Engine2D storage allocation,
swapchain acquisition, direct buffer-to-image transfer, then
`vkQueuePresentKHR`. Window and swapchain lifetimes are paired in the canonical
runtime registry. The event loop no longer exits before its first asynchronous
create request and shutdown is an explicit proxied event with a bounded create
response wait.

Under Xvfb with the llvmpipe ICD, a 320x180 live test completed two successive
same-device visible-window presentations and clean teardown. This is a
correctness/lifecycle result only: Xvfb is not a physical display, the test has
no 8K timing row, and it does not promote the physical NVIDIA lane.

## Physical-device 8K window probe

The same Xvfb window surface selected a real NVIDIA RTX A6000
(`vendor=000010de`, `device=00002230`, driver `911f8400`, Vulkan API
`00404138`) and native `IMMEDIATE` presentation mode. Twenty 7680x4320 frames
measured:

| Frame class | p50 ns | p95 ns | Budget |
|---|---:|---:|---:|
| Changed revision / full device copy | 72,705,486 | 78,768,041 | FAIL |
| Retained revision / seeded swapchain images | 67,359,848 | 70,119,663 | FAIL |

Peak RSS was 602,412 KiB. Both rows record zero device-to-host framebuffer
bytes, known completion, no CPU fallback, source checksum
14100917488874079107, and completed `vkQueuePresentKHR` calls. The unchanged
retained row avoids the Engine2D buffer copy yet remains about 67 ms, locating
the dominant cost in the NVIDIA-to-Xvfb visible presentation path rather than
DrawIR or framebuffer transfer.

This is physical-device execution but not physical-display evidence: Xvfb is a
virtual X server. The source checksum proves the immutable presented buffer,
not post-scanout pixels. An attached display/direct-scanout test with a device
origin readback or captured scanout checksum is still required before claiming
physical-GPU 8K/80 completion.
