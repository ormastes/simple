# Kimi execution plan: Simple 2D, Web, GUI, Skia and RenderDoc

Date: 2026-09-27  
Selection: feature C, evidence N2.  
Current release gate: `doc/09_report/verify_simple_2d_skia_renderdoc_hardening.md` says **STATUS: FAIL**.

## Objective and authority

Finish the selected shared DrawIR/UiIr, Engine2D Vulkan, optional upstream Skia
Ganesh Vulkan, Web case 02 and GUI scene work. Produce trustworthy executable
tests and completed pixel receipts. A Mac MoltenVK run is required for the Mac
lane; it adds evidence but does not replace NFR-2D-002's physical **Linux**
Vulkan run. Land only a reviewed, passing scope; do not turn a blocked row into
PASS because source or CPU validation exists.

Read these before editing: the final feature and NFR requirements in
`doc/02_requirements/{feature,nfr}/simple_2d_skia_renderdoc_hardening.md`,
`doc/04_architecture/simple_2d_skia_renderdoc_hardening.md`,
`doc/05_design/simple_2d_skia_renderdoc_hardening.md`,
`doc/03_plan/sys_test/simple_2d_skia_renderdoc_hardening.md`, the verification
report above, the Linux TODO at
`doc/08_tracking/todo/simple_2d_skia_renderdoc_linux_n2_2026-09-27.md`, and
`tools/upstream-skia-ganesh-vulkan/README.md`. The downloaded ZIP was
`/Users/ormastes/Downloads/simple_2d_skia_renderdoc_2026-09-25.zip`;
research already reconciled it with current source. Preserve the accepted
C/N2 selection and the predeclared case 02 oracle/tolerance.

## Worktree and verification rules

1. Inspect the current Git/jj state and identify this rendering lane's files
   before editing. The shared worktree contains many unrelated, partly staged
   changes and was detached at `664c80efda5` at the last scoped inspection;
   remote `main` was later. Use a dedicated checkout/worktree for publication
   and do not include another session's files in a commit.
2. Use the pure-Simple self-hosted runtime. `bin/simple` was a Rust seed symlink;
   the older Mac release binary falsely passed `expect(1).to_equal(2)`, and a
   newer one crashed before test execution. Do not treat prior green counts as
   evidence. Establish a deliberately failing matcher control before trusting
   focused specs or generated manuals.
3. Follow `AGENTS.md`: verify each acceptance criterion once after final edits,
   stop after at most three verify/fix cycles per feature, preserve build caches,
   and never loop over unchanged failures. Record a concrete blocker instead.

## Stage 1 — working Mac compiler and evidence runner

- Resolve the self-hosted Mac runner deployment. The isolated native verifier's
  third and final attempt ended with unresolved `_rt_cuda_*` and `_rt_vulkan_*`
  at arm64 link. The isolated verifier's
  `/private/tmp/simple_2d_verifier_20260926/build/mini_builds/renderdoc_test_runner.exit`
  records `native_build_exit=1`. Diagnose the missing runtime objects
  or entry-closure wiring from the retained linker log. Do not retry that same
  build command without a source or build-input correction.
- Produce a self-hosted executable whose failing-assertion control fails for
  the intended assertion. Then compile and run the changed DrawIR, bridge,
  producer, qualification and SPipe specs once; run docgen and retain logs.
- Exit evidence: binary path and SHA-256, exact source revision, negative
  control result, focused spec results, and generated-manual zero-stub receipt.

## Stage 2 — Mac Metal and MoltenVK device admission

- This M4 Mac reports `Metal: Supported`, an Aqua session and an active AGX
  accelerator. Inside the prior Codex command sandbox,
  `MTLCreateSystemDefaultDevice()` returned no device and Homebrew MoltenVK
  1.4.1's `vulkaninfo --summary` failed `VK_ERROR_INCOMPATIBLE_DRIVER` before
  instance creation. `ps` and system logs were also sandbox-denied. This is a
  process-access preflight, not a renderer verdict; no Mac Vulkan capture ran.
- From an approved process that can enumerate the GPU, record a Metal device
  name and a successful `vulkaninfo --summary` with the canonical
  `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`. No `sudo` is indicated by
  these observations. If either probe still fails, retain stdout/stderr and
  stop the GPU lane until device access is corrected.
- Run `scripts/check/check-macos-vulkan-2d-live-evidence.shs` once after that
  preflight. Retain its runtime/build receipts, complete readback image, device
  and driver identity, executable and ICD hashes, and failure logs. This
  generic Mac live harness is backend evidence, not the C/N2 scene comparison.
- Exit evidence: a MoltenVK device/driver receipt and completed Engine2D
  Vulkan pixels, with no CPU/software fallback or incomplete readback.

## Stage 3 — selected scenes and optional Skia on Mac

- Run the source-derived `01-solid-boxes`, `06-rectangular-clip` and
  `02-fractional-edges` scenes through the same admitted Engine2D Vulkan
  device. Keep exact RGBA for the first two and the already declared analytic
  interior/exterior and edge policy for case 02. Retain source indexes,
  DrawIR/UiIr v4 bytes, submitted affine matrix, color domain, complete
  top-left RGBA8 pixels, capture logs and hashes. Do not accept a placeholder
  device handle, GPU name alone, or an incomplete final target.
- The optional upstream Skia provider currently has only `build-linux.shs` and
  has not been compiled against the pinned checkout. First obtain the exact
  Skia revision `35d5edfa0d50984c22ff94f5438c31e0db12c6f8` and verified
  dependency manifest. Determine a Mac Ganesh/Vulkan/MoltenVK build from that
  revision; add a deterministic Mac build helper and receipt if supported.
  Keep the provider opt-in and outside default embedded linkage. Preserve
  private v3 validation, `f64` to submitted `f32` matrix provenance, surface
  clip order, AA policy, owned completion and teardown.
- Only after both Mac backends run the same source fixture on admitted devices,
  compare their completed pixels with the predeclared comparator. Mac parity
  remains a separate result from physical Linux N2 qualification.
- Exit evidence: two backend build/device/readback receipts, source-bound
  scene hashes, independent oracle verdict and RenderDoc capture where the
  Mac capture tool is available. If Mac RenderDoc is unavailable, record that
  separately; never substitute an image file for a RenderDoc capture claim.

## Stage 4 — Web and GUI completion

- Preserve Web case 02's real CSS producer inventory: background, canvas,
  rotated tile and fractional bar; verify transform order, surface clip and
  stable source indexes. Keep case 41's resolved element scroll and explicit
  viewport-fixed rejection. Run the 48-case corpus only with individual
  fixture manifests and comparators; unqualified rows stay `not-run`.
- The GUI input source scene pins Noto Sans Mono, but the upstream provider
  still rejects text and the source glyph IDs are not native vector-font glyph
  IDs. Define a bounded private native glyph contract, pinned font bytes,
  independent before/after caret and pixel oracle, then implement and run
  `31-latin-shaping` and GUI button/input scenes on both backends.
- Exit evidence: executable requirement-tagged Web/GUI specs, completed
  dual-backend pixels, input/visible-state receipts, font and fixture hashes,
  and explicit unsupported-feature errors where parity is not implemented.

## Stage 5 — physical Linux N2 and publication

- Follow the Linux TODO exactly: clean pinned Skia checkout, physical Vulkan
  GPU UUID/driver UUID, attested dependency and build receipts, separate
  Engine2D/Skia workers, completed readbacks, RenderDoc captures and scene
  verdicts. Mac MoltenVK evidence cannot satisfy NFR-2D-002.
- Run the requirement-traced SPipe gate and generated-manual review; update
  the verification report with actual artifact paths. Require `STATUS: PASS`
  before describing the selected scope as complete. Preserve unrelated dirty
  work and create a scoped commit in a clean publication lane.
- Fetch/rebase onto current `main`, open a PR with exact files and evidence,
  obtain normal review or the repository's exact-head SPipe Self Review
  Admission where eligible, then land only after required checks pass. A PR
  author cannot submit a GitHub `APPROVED` review on their own PR. No push or
  PR was made by the prior Codex session: shell Git could not resolve
  `github.com`, and the GitHub app write was rejected under approval policy
  `never`. Recheck those external gates before publication; do not bypass them.

## Done checklist

| Criterion | Required proof |
|---|---|
| Mac compiler | Self-hosted executable, failing-assertion control, focused specs/docgen |
| Mac Vulkan | Metal device, MoltenVK device, live Engine2D readback receipt |
| Mac selected scenes | Source-bound case 01/06/02 pixels and comparator verdicts |
| Optional Skia on Mac | Pinned checkout/deps, deterministic build, provider pixels and lifetime evidence |
| Web and GUI | Real producer/input scenes and admitted two-backend outputs |
| Linux N2 | Physical Linux GPU identity and completed dual-backend captures |
| Merge | Verification PASS, scoped PR, required checks, landed commit |

Kimi owns implementation and evidence collection in its lane. The merge owner
must review the final diff and evidence against the accepted requirements;
source inspection, CPU validation and a Mac-only GPU run are not completion
evidence for the Linux N2 gate.
