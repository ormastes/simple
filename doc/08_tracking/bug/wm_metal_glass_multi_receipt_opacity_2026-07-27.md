# WM Metal Glass Multi-Receipt and Inactive Opacity
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** source fixed and independently accepted / runtime unverified
**Affected lane:** hosted WM `DrawIrComposition -> Engine2D -> Metal`

The rejected WM glass candidate had three source defects:

1. Inactive opacity (`930`) creates a shared Metal offscreen with
   `gpu_only=false`; the device-glass operation rejects that surface, so the
   intended Metal path cannot complete.
2. Material receipt counts aggregate, but target/framebuffer handle/device
   identity are last-wins. The host therefore validates only the final receipt,
   not every requested material against the presented framebuffer.
3. A focused window-scene test expects
   `engine2d-cpu-rounded-material-v1` while production emits
   `engine2d-rounded-material-v1`.

The repaired source now gives `MetalBackend` one persistent session-owned
device identity, preserves it through device readback and every material
receipt, independently derives the ordered requested material IDs from the
submitted composition, and validates each receipt against the presented
framebuffer. Missing, duplicate, extra, reordered, unfulfilled, mixed-target,
handle, device, source, and checksum mismatches fail closed.

CPU seeded/delta composition preserves parent sampling and tested 500/930
opacity. Selected Metal explicitly rejects sub-opaque parent-sampling material
before dispatch until a true GPU-only delta path exists; it cannot claim a
Metal product frame through a mirror-backed offscreen. Requested blur 30 /
bounded CPU realization 4 remains explicit. Focused behavioral contracts and
independent highest-capability review found no remaining P0/P1 source issue.

## Remaining runtime verification

- With an admitted self-hosted runtime, run the exact focused contracts in a
  fresh scoped session:

  ```sh
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_readback_handle_contract_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl --mode=interpreter
  bin/simple test test/01_unit/os/compositor/host_compositor_entry_spec.spl --mode=interpreter
  ```

  Then obtain admitted macOS opaque-Metal device readback/capture evidence and
  retain the ordered per-material receipts. Inactive/sub-opaque Metal must
  remain an explicit fail-closed capability row until a GPU-only delta path is
  implemented and independently verified.

## 2026-09-22 scoped macOS admission evidence

Status remains **source fixed / runtime unverified**. This audit used an
isolated checkout of PR #1207 at `3ee03891f9a`; observed `origin/main` was
`e0dd873da1b`. No production source or SoSIX interface was changed.

One invocation of `sh scripts/check/build-macos-gpu-2d-live-native.shs --build metal`
stopped with `FAIL (canonical-stage3-compiler-missing)` before compiler launch.
`/usr/bin/time -l` measured 0.04 seconds elapsed and 7,012,352 bytes maximum
resident set size. This is admission-command resource evidence only, not GPU
performance or a process-tree memory-limit qualification. No bootstrap was
started and no focused contract or native GPU assertion executed.

Retained admission output (the original log is
`/tmp/mac-metal-runtime-admission-20260922.log`):

```text
macOS GPU 2D native build: FAIL (canonical-stage3-compiler-missing)
        0.04 real         0.02 user         0.01 sys
             7012352  maximum resident set size
             4129104  peak memory footprint
```

The wrapper printed the log afterward, so its reported shell exit zero belongs
to the log display; the builder's exit status was not separately retained.
The explicit admission failure above is the result, not a successful build.

The native builder requires both `simple` and `provenance.env` under
`build/wm-to-i64-bootstrap/stage3/aarch64-apple-darwin/`; neither is present
in this isolated checkout or the shared root. A Stage2 compiler or the root
`bin/simple` symlink to the Rust bootstrap seed cannot satisfy that gate.
The missing artifacts must come from the coordinated admitted producer;
do not bypass provenance or start a competing bootstrap for this row.

Before closing this row, retain the five focused contract results above and
native evidence that explicitly requires `backend_name() == "metal"`.
`backend_metal_device_identity_spec.spl` currently permits unavailable Metal
to take a passing fallback branch, so its green result alone cannot establish
device execution. The generic macOS GPU 2D live harness records device
readback/checksums but does not assert glass-material receipts.

The required native glass evidence must assert two ordered opaque material
IDs against the same positive framebuffer handle and device identity, fulfilled
counts, and device-readback source/checksum. It must also assert that inactive
opacity 930 dispatches zero material commands while retaining two ordered
unfulfilled receipts. Profile the actual admitted execution under the shared
6 GB resource guard, retain its timeout/exit/RSS receipt and capture, and keep
sub-opaque Metal explicitly unsupported. These checks remain pending; this
admission failure does not demonstrate a new Metal defect or a resolved row.

## Strict native fixture candidate (runtime UNRUN)

`test/02_integration/rendering/macos_metal_glass_receipts_native.spl` is a
standalone native executable entry. Unlike the portable unit spec, it exits
nonzero when the selected backend is not Metal. It requires two ordered,
fulfilled opaque material receipts bound to the rendered framebuffer and
device, compares the captured pixels with independent white/black region
oracles, and compares the receipts' checksums with a second device readback.
Two inactive opacity-930 passes, with material alpha 1000 and 500 respectively,
each require zero dispatch, two ordered unfulfilled receipts, and unchanged
framebuffer pixels and identity. The first varies only embedding opacity from
the accepted active case: material-alpha rejection cannot mask a broken
opacity gate. The second preserves the original translucent-material case.

Related open TODOs 8 and 9 need actual Metal provider evidence, which this
fixture can contribute only after native admission and execution. TODOs
10–12 and 173 concerning lifecycle/fence/timestamp evidence are not established
by synchronous readback; neither receipt checksums nor wall-clock timing are
GPU timestamps. No TODO or bug row is closed by this source candidate.

### Bounded execution and profiling recipe

Run only after the canonical Metal trusted-build manifest has been produced
by the coordinated Stage3 owner. These commands intentionally fail on missing
or invalid admission; do not substitute the seed. The first guard covers the
native build and the second covers execution. Use a fresh evidence directory
for each authorized attempt; do not rerun a passing check.

```sh
set -eu
. scripts/check/lib/macos-gpu-trusted-build-admission.shs
macos_gpu_trusted_manifest_admit \
  "$PWD/build/macos_gpu_2d_live_native/metal/trusted-build.env" metal "$PWD"
metal_evidence_dir=$(mktemp -d "$PWD/build/metal-glass-evidence.XXXXXX")
metal_entry=test/02_integration/rendering/macos_metal_glass_receipts_native.spl
# This branch does not contain the resource guard. Use the reviewed external
# supervisor without changing or importing the compiler/Metal source snapshot.
METAL_RSS_GUARD=/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/scripts/resource/process-tree-rss-watchdog.pl
test -f "$METAL_RSS_GUARD"
shasum -a 256 "$METAL_RSS_GUARD" >"$metal_evidence_dir/guard.sha256"
perl "$METAL_RSS_GUARD" \
  --max-rss-kib=5859375 --rss-cap-mode=enforce --interval-ms=100 --timeout-seconds=240 \
  --receipt="$metal_evidence_dir/build.rss.env" -- \
  /usr/bin/time -l env SIMPLE_LIB="$PWD/src" SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_LINK_OBJECTS="$MACOS_GPU_ADMISSION_PROVIDER:$MACOS_GPU_ADMISSION_RUNTIME_C_PROVIDER" \
  "$MACOS_GPU_ADMISSION_COMPILER" native-build --backend cranelift --threads 4 \
  --cache-dir "$metal_evidence_dir/cache" --runtime-bundle core-c-bootstrap \
  --source src/lib --source test/02_integration/rendering --entry-closure \
  --entry "$metal_entry" --strip --output "$metal_evidence_dir/probe" \
  >"$metal_evidence_dir/build.stdout" 2>"$metal_evidence_dir/build.stderr"
perl "$METAL_RSS_GUARD" \
  --max-rss-kib=5859375 --rss-cap-mode=enforce --interval-ms=100 --timeout-seconds=30 \
  --receipt="$metal_evidence_dir/run.rss.env" -- \
  /usr/bin/time -l env DYLD_PRINT_LIBRARIES=1 \
  DYLD_LIBRARY_PATH="$(dirname "$MACOS_GPU_ADMISSION_PROVIDER"):$(dirname "$MACOS_GPU_ADMISSION_RUNTIME_C_PROVIDER")" \
  "$metal_evidence_dir/probe" \
  >"$metal_evidence_dir/run.stdout" 2>"$metal_evidence_dir/run.stderr"
```

Retain exit status, both guard receipts, timing stderr, loaded-provider paths,
all six material receipt lines, and the final PASS/FAIL line. Require expected
provider resolution and guard quiescence before accepting evidence. The RSS
guard monitors a sampled process tree under decimal 6 GB; it is not a kernel
hard limit. This 4x4 correctness probe's wall time/RSS does not qualify realistic
WM frame latency, blur throughput, or GPU memory use.

SoSIX review: the fixture adds no extern, environment, process-launch, or IO
facade implementation. It calls existing Engine2D APIs and prints evidence;
the recipe uses existing admission and resource-guard owners. No SoSIX API or
ABI changes. Native compile/syntax and runtime checks remain UNRUN until the
admitted producer is available; source review cannot replace them.

## Restored agent lane — 2026-09-22 08:22 UTC

The deleted worktree was reconstructed from preserved branch
`docs/mac-metal-runtime-evidence-20260922` at
`0f2a6e4d0178e8e313890b9790994b19291cd8d1` into
`/Users/ormastes/simple-tmp/mac-metal-runtime-20260922`. The checkout was clean
before the following admission probe. Existing native fixture SHA-256:
`9558895da9724a67098d790c50596fa7ae30c40a8ba2ed701b727499d99ebb19`.

One fresh `build-macos-gpu-2d-live-native.shs --build metal` admission probe,
wrapped by the external process-tree watchdog with explicit enforcement at
5,859,375 KiB and a 30-second timeout, returned **exit 1**:
`canonical-stage3-compiler-missing`. Evidence is retained in
`build/metal-glass-evidence-20260922-restored/{admission.stdout,admission.stderr,admission.rss.env}`.
This is an admission failure before compilation, not a Metal test failure.

- Host: macOS 26.5 (25F71), arm64, 10 logical CPUs, 25,769,803,776 bytes RAM.
- Wall time: 0.06 seconds; `time -l` maximum RSS: 7,143,424 bytes.
- Sampled process-tree peak: 2,464 KiB across five samples; receipt reports
  `status=complete`, `exit_status=1`, `quiescent=1`, `rss_cap_enforced=1`, and
  `hard_memory_limit=0`. The short probe's sampled peak does not replace the
  child lifetime maximum and is not a GPU or compiler memory measurement.
- External watchdog SHA-256:
  `69349c788f20f2f4052ae7e852baea59ce836c71fa65fad3b6c4226700e1c64f`.

The canonical builder requires an executable **and root-bound provenance** at
`build/wm-to-i64-bootstrap/stage3/aarch64-apple-darwin/{simple,provenance.env}`.
The coordinated bootstrap owner must provide a legitimately admitted producer
through that ownership path before native execution. Copying a binary alone,
using Stage 2, or using the seed does not satisfy admission. No provider,
device, native regression, performance, or memory claim is made from this
preflight. No production source change or bug closure was justified by it.

The strict fixture remains the positive native regression and the opacity-930
zero-dispatch/unchanged-pixels negative control. The focused host compositor
spec separately rejects a mismatched **first** receipt even when the last one
matches, plus missing, duplicate, reordered, extra and unfulfilled receipts.
Both still require admitted execution; source assertions are not PASS evidence.

### Follow-up: isolate the opacity regression

The strict fixture now executes the additional opacity-930/material-alpha-1000
negative control described above. It reuses the same 4x4 engine and performs
one additional bounded composition/readback; production paths are unchanged.
Its final success row is
`metal_glass_status=PASS active_receipts=2 inactive_receipts=4 inactive_cases=2 pixels=16`.
This is a test candidate, not an execution result. Native syntax, receipts and
pixels remain unverified until the coordinated admitted producer is available.

### Root-bound producer integration route

`build-macos-gpu-2d-live-native.shs` requires the compiler and provenance at
`$ROOT_DIR/build/wm-to-i64-bootstrap/stage3/<host-triple>/` in both its build
and manifest-verification paths. The restored P0 run instead selects
`build/bootstrap/macos-enforced-bd544-stage2` as its bootstrap output root;
its subsequent Stage 3 path is beneath that output. These paths are not
interchangeable: the Stage 3 verifier binds canonical repository root, output
path, inode/hash, source snapshot, command transcripts and recorded authority.

The integration owner must either produce Stage 3 at the consumer's canonical
root/path, or review a consumer change admitting the actual immutable P0
origin through the complete existing verifier in both build and verification.
Do not edit manifest fields, copy/symlink a compiler into the legacy path, or
start a second bootstrap solely for this fixture. Coordinate source integration
before producer snapshots are frozen; preserve an active build's frozen source.
The strict fixture is absent from the reconstructed P0 checkout at this audit,
so its reviewed source/hash must also be included in the consumer build inputs.

After producer admission, the owner must build the normal Metal trusted
manifest, with its bound `build/sffi/{libspl_winit,libsimple_runtime_wm,libsimple_runtime_c_wm}.dylib`
providers, before the strict native recipe above is eligible. Retain provider
hashes and actual dynamic-loader resolution. Stage 2 admission, a raw Stage 3
binary, an old trusted manifest, or portable unit tests alone cannot satisfy
this route. The Metal lane does not author or mint its own producer receipts.

## 2026-11-04 native macOS run (lane 4)

Tree release/1.0.0 `1ebaf7d1e1f`, seed `/Users/ormastes/.local/share/simple-seeds/release100-7a0e6fe516f-20261031/simple`, `--mode=interpreter`:
- backend_metal_device_identity 2/2, backend_readback_handle_contract 1/1 PASS.
- draw_ir_adv 68/70: red "submits a GPU-selected Draw IR batch through the
  runtime host GPU queue" (expected false to equal true) and "stages retained
  Vulkan composition damage for a partial host refresh" (expected 4278190080
  to equal 4294901760).
- window_scene_draw_ir 4/12 and host_compositor_entry 42/61: UNRUNNABLE on
  release/1.0.0 — see
  `spec_helpers_dropped_by_release_transplant_88aac2ffe28_2026-11-04.md`.
Native gate (`build-macos-gpu-2d-live-native.shs --build metal`) needs the
admitted full-CLI (Lane 1). Status unchanged: source fixed / runtime unverified.

## 2026-11-04 — acceptance specs reconciled on release/1.0.0 (macOS M4, seed interpreter)

Status: **fix-implemented / verification-pending** (native Metal not run).

Binary: `~/.local/share/simple-seeds/release100-7a0e6fe516f-20261031/simple`
(Rust seed, interpreter). No admitted self-hosted macOS Stage 2 exists
(`/private/tmp/lanes/stage_artifacts.txt`: lane1 s2d built, sanity refused),
so the Metal native path could not be exercised; the receipt/opacity
validation below is covered only through the interpreter.

Changes:
- `window_scene_draw_ir_spec`: restored the helpers, imports and in-body
  locals dropped by transplant `88aac2ffe28`/`bb3f6ab8ab2` (from
  `88aac2ffe28~1`), then reconciled to current source: `maximize-state`
  text command (added `31d21e30f82`, 2026-08-25) shifts window indices and
  counts (9->10 legacy, 8->9 themed, plan 34->36); focused-window titlebar is
  `title_focused`; resolved-font title style index 2 is `font-size` and the
  advance list moved to `advance_widths`; engine bitmap fallback is now gated
  by `has_ttf`. **12/12 pass** (was 4/12).
- `host_compositor_entry_spec`: restored from `88aac2ffe28~1` (helpers,
  imports, receipt fixtures) and reconciled: provenance evidence now reads
  `last_readback_source/last_backend_handle/last_readback_checksum`
  (raw-string contract), requested attempt is
  `render_draw_ir_composition_from_retained_damage` (`fd085136a6d`),
  recompose fixture uses a local-web owner (owner port 0; a positive port is
  renderer-owned since `553ea5aae8e`) and a 64x60 window so content fits.
  **55/63** (was 42/61). All Metal receipt cases pass (exact pair, missing,
  duplicate, reordered, extra, unfulfilled, inactive fail-closed).
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl`: restored
  `Engine2D.window_present_enabled()` (added `d2b1f7b2235`, deleted by the
  stale-snapshot commit `8a87db7d9eb`); `host_compositor_core.spl` and
  `hosted_entry.spl` call it on every Engine2D frame, so any hosted Draw IR
  frame failed with `method window_present_enabled not found`.

Remaining reds (not weakened, recorded):
- host `recomposes a rejected host GPU material frame`: the fixture fakes
  Metal via `selected_backend_name = "metal"` on a CPU engine; the CPU
  recompose still creates offscreens via `backend_name()=="metal"` ->
  `create_shared_metal_offscreen` -> `shared-metal-parent-required`. Needs an
  owner decision: real Metal engine fixture (native lane) vs routing on
  `metal_backend` presence.
- host: 7 other reds unrelated to Metal glass (taskbar `contains` arity and
  `cannot assign to const 'comp'` are seed-interpreter semantics; chrome
  pixel/theme color, wheel delta, cache release, display-app input).
- `draw_ir_adv_spec` 68/70: both reds are Vulkan/host-GPU-queue cases, not
  Metal glass. `8a87db7d9eb` also deleted `Engine2D.vulkan_present_readback_bytes`,
  `stage_present_damage`, `finalize_compute_frame_no_readback`,
  `present_window_device`, `latest_vulkan_frame_receipt`,
  `read_pixels_damaged`, `invalidate_damage_mirror`,
  `create_vulkan_window_present`, `create_vulkan_external_window_present`
  (all still have callers) — Vulkan owner must restore them.
