# Optional provider qualification status

Status: **BLOCKED_ENVIRONMENT** (2026-09-26, macOS arm64 workspace; refreshed
2026-09-27).

- 2026-09-27: `build-macos.shs` added (deterministic Darwin twin of
  `build-linux.shs`). Guard paths tested (exit 2 without `SKIA_ROOT`). The full
  build is untested because the pinned checkout is still absent. The macOS
  prerequisites probe passed: Vulkan loader, MoltenVK 1.4.1 ICD, ninja,
  clang++, in-checkout gn. A Mac build remains backend evidence, not Linux N2
  qualification.
- 2026-09-27 (later): the pinned Skia checkout now EXISTS at
  `/private/tmp/simple-skia-pinned-2026-09-27` — exact revision
  `35d5edfa0d50984c22ff94f5438c31e0db12c6f8`, clean worktree, 44 externals
  synced via `tools/git-sync-deps` (gn arm64 v2175 verified). The dependency
  attestation initially rejected `third_party/externals/perfetto` because the
  DEPS pin is an annotated *tag* object while the verifier compared raw commit
  hashes; `verify-skia-deps.py` now peels pins to commits
  (`rev-parse <pin>^{commit}`) and attests all 45 Git dependencies
  (checkout-manifest digest `28e98416c16419a904936309ec00667df6bf0a1058ac0ab55229e1353c90c666`,
  manifest retained at `/private/tmp/skia-deps-manifest.json`).
- 2026-09-27 (evening): **the macOS provider is built and device-verified** —
  `build/optional/libsimple_upstream_skia_ganesh_vulkan.dylib`
  (provider_sha256 `3320c460…73957`) with a complete receipt (pinned revision,
  DEPS digest, 45 attested checkouts, archive hash, affine_v3=0, Vulkan loader
  and MoltenVK digests). Four fixes made this possible: the dependency sync is
  now attest-gated (a re-sync runs irrelevant DEPS hooks such as Emscripten
  activation that can abort a complete checkout); `provider.cpp` compiles with
  `-DSK_USE_INTERNAL_VULKAN_HEADERS` and `-I$SKIA_ROOT/include/third_party/vulkan`
  (Skia's in-tree Vulkan headers); the Darwin link adds `CoreServices` for the
  dng_sdk text APIs; and `create_vulkan` enables
  `VK_KHR_portability_enumeration` on Apple — without it the loader hides
  MoltenVK and `session_open` rejects (native ICDs are unaffected).
  `libskia.a` (1331 targets) compiled clean. **Device evidence (backend lane
  only, not Linux N2)**: the standalone ABI probe
  `build/optional/skia_device_probe.c` rendered a 64×64 solid-boxes scene on the
  admitted MoltenVK device (canonical ICD), completed GPU work
  (`device_elapsed_ns` ≈ 19–456 ms across runs), read back 4096 RGBA pixels with
  **zero analytic mismatches**, matched the receipt's FNV-1a-64 checksum
  (`de229a93cc509325`), and retired completion/resource/session cleanly
  (probe source + full pixel dump: `build/optional/skia_device_probe_run1.log`).
- 2026-09-27 (night): **pinned scene oracles matched on the MoltenVK device**.
  The scene probe `build/optional/skia_scene_probe.c` ran the source-derived
  corpus scenes through the pinned provider on the admitted device:
  `case01-solid-boxes` (v1, white clear + red/blue/green boxes) readback
  SHA-256 `2f4d3fb1…39e9` and `case06-rectangular-clip` (v2, cyan rect clipped
  to 80,65,120,75) readback SHA-256 `0372ef52…ebb1` — both **exact matches**
  with the independent authored-CSS oracle digests
  (`src/lib/common/renderdoc/corpus_case{01,06}_oracle.spl`), clean
  completion/resource/session retirement, GPU elapsed 13–28 ms
  (log: `build/optional/skia_scene_probe_run1.log`). Case 06's rect fully
  covers its clip, so any covering geometry yields the pinned visible result;
  the oracle pins the visible clip-policy evidence.
- 2026-09-27 (night): **case 02 v3 candidate measured on-device with
  submitted-matrix provenance** (`build/optional/skia_case02_probe.c` against
  the affine-v3-enabled build `…_v3.dylib`, receipt `affine_v3_enabled=1`,
  provider sha `ffe83312…`). Provenance recorded: source f64
  (a=0.99254615164132198 b=0.12186934340514748 c=-b d=a
  tx=47.266176984628068 ty=40.123984175619334), submitted f32, max
  transformed-corner error 0.000434 px (bound 0.125). Device verdict
  (independent analytic area oracle): interior/exterior **exact**
  (`exact_mismatch=0`), bar regions exact (558 interior / 285 edge), edge
  mean channel delta 0.0149 (bound 4.0) — but **4 of 914 edge pixels exceed
  the predeclared 16-channel-delta bound (max 30), and 86 tile pixels move
  between ideal-full and ideal-partial vs Skia's coverage rasterizer, so the
  comparator reports FAIL** (`passed=0`). Recorded as a measured tolerance
  exceedance, not fudged: Skia's coverage-AA edge treatment of the rotated
  tile deviates from the ideal area model slightly more than the predeclared
  case02 tolerance allows (log: `build/optional/skia_case02_probe_run1.log`).
  Follow-up options: owner decision whether the predeclared tolerance should
  accommodate rasterizer-specific edge policy, or the v3 execution sequence
  should align coverage with the area model. The default v1/v2 scenes remain
  exact.
- 2026-09-27 (night): **identity export verified and v1/v2 reproducibility
  confirmed across builds**. The identity probe  (`build/optional/skia_identity_probe.c`) exercised the optional
  session/completion-bound export: it fails closed before any completion
  (status -3) and, after a real completed+observed readback on the admitted
  device, returns version 1 with device_uuid `0000106b1a040209…` and
  driver_uuid `4d564b00000028a1…` — **exact matches** with the preflight-bound
  MoltenVK identity (vendor 0x106b, driver 10401 = MoltenVK 1.4.1 encoding);
  clean session close (log: `build/optional/skia_identity_probe_run1.log`).
  Independently, the v1/v2 scene probes run against the affine-v3-enabled
  build reproduce byte-identical oracle hashes (`2f4d3fb1…39e9`,
  `0372ef52…ebb1`), confirming the v3 opt-in only widens acceptance. The
  optional Skia macOS lane now has: pinned checkout + attested deps, two
  deterministic builds (default and v3) with receipts, three device-rendered
  scenes with independent verdicts, identity binding, and a measured case02
  tolerance finding. What remains for it is the physical Linux N2 run and the
  owner decision on the case02 edge tolerance.
- 2026-09-27 (night): **fail-closed fault behaviors device-verified** (19/19
  checks, `build/optional/skia_fault_probe.c` +
  `skia_fault_probe_run1.log`, upgrading three previously static-review-only
  items): a truncated `submit` struct is rejected before its (here bogus)
  output-resource field is read, with no completion created; a malformed draw
  magic is rejected with clean resource/session retirement; and
  `session_close()` returns BUSY while a completion or resource child is
  outstanding — the session remains fully usable after a BUSY answer and
  retires cleanly only after `completion_release` then `resource_release` in
  the admitted order.
- Running `build-linux.shs` on macOS exits 2 with `macOS build required`;
  `build-macos.shs` is the Darwin entrypoint. No physical Linux Vulkan
  device, GPU completion, native readback, or RenderDoc capture was exercised
  here; `REQ-2D-005` and the NFR-2D-002 Linux qualification remain open.
- The source now requests sRGB for both render target and readback and disables
  rectangle antialiasing; pixel parity and the exact pinned-header build remain
  unverified here.
- The provider releases its global map lock during synchronous GPU work, while
  a per-session busy state prevents retirement of the active session or
  resource. This has static review only; no pinned-Skia build or device run
  has verified the change.
- `session_close()` now permits teardown after `VK_ERROR_DEVICE_LOST` once
  child resources and completions have been retired, releasing Ganesh resources
  before destroying the still-live Vulkan handles. A lost session remains
  unusable for rendering. Native fault injection must verify lost-device close,
  child-busy refusal, and empty provider state after shutdown.
- `submit()` rejects a truncated ABI request before reading its output-resource
  field. A native malformed-struct-size test remains required on the pinned
  provider build.
- Private drawing payload v2 adds per-rectangle target-coordinate clips while
  preserving v1. The native validator checks format, magic, exact length,
  flags, clip dimensions, representable edges, and an unclipped first clear
  before Skia records work. Draws use balanced clip state. Header syntax checks
  passed in C11 and C++17; pinned-Skia compilation, state-leak regression,
  independent clipped-pixel oracle, and physical Vulkan parity remain open.
- Private payload v3 has a 128-byte affine/raster contract and a CPU-only
  shape validator, including the predeclared 0.125-pixel transformed-corner
  conversion bound. The experimental native draw sequence now saves canvas
  state, clips in target space, concatenates the affine matrix, applies the
  raster AA policy, draws the local rectangle, and restores state before the
  existing flush/submit/completed-readback tail. Its compile-time gate defaults
  off, so default native `submit()` and Simple preflight still reject v3 before
  GPU work. Submitted-matrix provenance, pinned-header compilation, and
  physical case02 readback remain open.
- `build-linux.shs` now accepts the explicit
  `SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3=1` experimental build opt-in and
  records `affine_v3_enabled` in the build receipt. The default is `0`; an
  opted-in build is still only a candidate until the pinned Skia build,
  submitted-matrix provenance, and physical case02 pixels are verified. The
  physical runner requires this field to be exactly `1` for case02 and binds
  the receipt hash to the run.
- The Linux build helper now forces the pinned `DEPS` path, checks each enabled
  Git dependency's HEAD and clean worktree after sync and after the Skia build,
  and records a deterministic checkout manifest/digest. The physical runner's
  receipt bound now admits that manifest and requires its digest. This gate has a local
  synthetic Git test; it has not yet run against the pinned Skia checkout.
- `submit()` still has no finite timeout. The adapter's five-second `wait()`
  timeout cannot interrupt blocked submission, device idle, or readback.
  `device_elapsed_ns` is host elapsed time, including CPU work and waits,
  rather than a device GPU timestamp.
- C++ allocation and rendering paths now return a fail-closed ABI status on
  exceptions instead of letting them escape through `session_open`,
  `resource_alloc`, or `submit`. This containment is statically reviewed only;
  fault injection and native compilation remain open.
- The optional identity export now records Vulkan 1.1 device/driver UUIDs from
  the selected physical device and answers only for an owned, waited
  completion whose readback was observed. The authenticated host loader gates
  the query on the same completed owner state without changing ABI v1. Simple
  copies the UUIDs into its Skia frame before retirement. C11 syntax checks
  passed, but the Linux integration runner and pinned Skia compilation have
  not run here; macOS lacks the loader's sealed-memfd admission path.
- The `bin/release/macos-arm64/simple` runner reported 5/5, but an independent
  intentionally failing assertion also reported PASS through that binary.
  This result is **invalid evidence**. The bootstrap `bin/simple` runner died
  before executing the spec. No trustworthy Simple test PASS is claimed.
  C/C++ header syntax and shell parser checks are static contract evidence only.

On an admitted Linux host, run `build-linux.shs` with `SKIA_ROOT` set to the
exact `skia-pin.json` revision, retain its `.receipt.json`, then record the
physical Vulkan properties, wrong-thread/device-loss/close behavior, completed
RGBA readback, and capture provenance. Use separate authenticated processes
for upstream Skia and the existing Vulkan backend.

- 2026-09-27 (late): macOS MoltenVK pinning is now reproducible. New
  source-only helper `env-moltenvk.shs` exports `VK_ICD_FILENAMES` bound to
  the canonical ICD `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json` and
  fails closed on ICD/library SHA-256 drift from the stage-2 preflight
  receipt. All macOS device/scene/fault probes of this lane must run under
  this pin; the full live harness applies the identical pin in
  `scripts/check/check-macos-gpu-2d-live-evidence.shs`.
