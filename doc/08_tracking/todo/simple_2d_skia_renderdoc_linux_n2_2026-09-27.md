# TODO: [2D][N2] Qualify the selected C path on physical Linux Vulkan

Date: 2026-09-27  
Status: BLOCKED — physical Linux host (NVIDIA GB10) and pinned Skia provider build now exist (2026-11-18); no native pure-Simple qualification executable, so no worker readbacks.
Scope: REQ-2D-003, REQ-2D-005, REQ-2D-006, NFR-2D-002.

Use a physical Linux host with an identified discrete or integrated Vulkan GPU.
Record its OS, GPU vendor/device, driver and API versions, device UUID, and
driver UUID. Obtain a clean Skia checkout at
`35d5edfa0d50984c22ff94f5438c31e0db12c6f8`. Build the optional provider
with `SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3=1` through
`tools/upstream-skia-ganesh-vulkan/build-linux.shs`; retain the provider binary,
its build receipt, dependency checkout manifest, and exact SHA-256 digests.

Build the current pure-Simple qualification executable on Linux. Establish a
failing-assertion control before trusting SPipe. Run the isolated Engine2D and
Skia workers on the same selected physical device for `01-solid-boxes`,
`06-rectangular-clip`, and `02-fractional-edges`; retain completed top-left
RGBA8 readbacks, worker logs, receipts, and RenderDoc captures. Check exact
pixels where specified and the predeclared analytic edge tolerance for case 02.
Reject CPU fallback, incomplete submissions, mismatched device identities,
missing submitted-matrix provenance, or build/receipt digest changes.

After the private native glyph contract, independent oracle, and declared
tolerance exist, add `31-latin-shaping` and the GUI input before/after states.
Keep those rows and the remaining corpus rows `not-run` until individually
qualified. Run the requirement-traced SPipe and generated-manual gates, then
update `doc/09_report/verify_simple_2d_skia_renderdoc_hardening.md` with the
actual Linux artifacts. Do not promote a Mac source check to N2 device evidence.

References: `doc/03_plan/sys_test/simple_2d_skia_renderdoc_hardening.md` and
`tools/upstream-skia-ganesh-vulkan/README.md`. Supply host connection details
through secure configuration, not this document.

Update (2026-09-27): the macOS side has produced everything the Linux lane
can reuse. The pinned Skia checkout at
`/private/tmp/simple-skia-pinned-2026-09-27` (exact revision
`35d5edfa0d50984c22ff94f5438c31e0db12c6f8`) has 45 attested Git dependencies
(checkout-manifest digest `28e98416…c666`); `verify-skia-deps.py` now peels
annotated-tag pins. `build-linux.shs` shares both fixes via the same
verifier; run it on the Linux host with `SKIA_ROOT` pointed at a fresh
synced checkout there (do not copy the macOS build outputs — rebuild so the
archive/provider digests bind to the Linux toolchain). The case01/case06
oracle digests (`2f4d3fb1…39e9`, `0372ef52…ebb1`) and the case02 analytic
comparator are platform-independent references already validated on the Mac
backend lane; case02 has one open owner-decision bug
(`doc/08_tracking/bug/skia_case02_edge_tolerance_exceedance_2026-09-27.md`).
The Engine2D/Vulkan and bootstrap lanes remain gated on
`doc/08_tracking/bug/macos_stage2_compiler_cli_build_host_gpu_link_2026-09-27.md`.

Update (2026-09-27, late): macOS MoltenVK is now reproducibly pinned for
this lane via `tools/upstream-skia-ganesh-vulkan/env-moltenvk.shs`
(canonical ICD + digest fail-closed). The full Linux test-execution
checklist (corpus, gates, RenderDoc) lives in
`doc/08_tracking/todo/simple_2d_linux_vulkan_tests_2026-09-27.md`; this
document remains the device-qualification half.

Update (2026-11-18, physical Linux GB10): the "no physical Linux Vulkan host"
half of the block is gone. On an aarch64 Ubuntu 24.04 host with an NVIDIA GB10
(integrated, Vulkan 1.4.312, driver 580.173.02, deviceUUID
`1883ff9c30a91b8abc50ef34ac2f5a89`, driverUUID
`6d5e1e1841115cbdae1ec369f9e3c390`) the pinned Skia checkout was synced (45
attested deps, digest `28e98416…c666`, identical to macOS) and the provider
built with `SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3=1` (provider sha256
`758f717f…bc89`, libskia.a `f368cf7b…f60a`, receipt
`doc/09_report/linux_gb10_skia_provider_receipt_2026-11-18.json`).
`build-linux.shs` gained clang/llvm-ar GN toolchain args, bundled FreeType
with fontconfig off, in-tree Vulkan headers, `-l:libvulkan.so.1`, attest-gated
sync and an opt-in ninja job bound. The seed passed a failing-assertion
control. A RenderDoc capture of the generic Engine2D scene on the GB10
succeeded (2 of 3 tries; `vkCreateDevice` under the layer fails
intermittently with `-3`, it is not a hard rejection).

Still BLOCKED: no native qualification executable — no self-hosted release
binary exists on the host, and the seed's `native-build` of the runner did not
produce one (details in
`doc/09_report/linux_gb10_skia_n2_qualification_2026-11-18.md`). The seed
interpreter cannot host the workers either (`main.spl:67:9 value is not
callable`). So cases 01/06/02 have no GB10 readbacks and stay `not-run`. The
N2 workers also cannot be RenderDoc-captured until the runner or provider
calls the in-app start/end capture API. Next: deploy a self-hosted aarch64
release binary, build the runner with it, and run
`run-corpus-case01|06|02` with `VK_DRIVER_FILES` pinned to the NVIDIA ICD.

Update (2026-11-18, follow-up): the original `build/` artifacts were lost to a
worktree cleanup and were regenerated under `/home/yoon/skia-n2/artifacts/`.
The provider was relinked from the surviving `libskia.a` to the same sha256,
`758f717f…bc89`. A new GB10 Engine2D RenderDoc capture was taken
(`ab1bd6af…e3a9`, replay-open verified). The two executable blockers are
filed in
`doc/08_tracking/bug/linux_gb10_n2_qualification_executable_blockers_2026-11-18.md`.
Status unchanged: BLOCKED.
