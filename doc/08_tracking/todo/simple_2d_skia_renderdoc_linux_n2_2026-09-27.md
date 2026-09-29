# TODO: [2D][N2] Qualify the selected C path on physical Linux Vulkan

Date: 2026-09-27  
Status: BLOCKED — no physical Linux Vulkan host or pinned Skia checkout has been supplied.  
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
