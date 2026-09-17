# WM Web 2D Retained Perf Evidence — 2026-09-17

Retained evidence gate for
`doc/08_tracking/bug/gui_web_2d_retained_metal_simd_wm_perf_evidence_gap_2026-07-06.md`,
produced by `scripts/check/check-wm-web2d-retained-perf-evidence.shs` (gate run of
2026-09-17, stdout transcript `build/wm-web2d-retained-probe/full_run6.log`).

The hosted-WM lane launches the web showcase from the filesystem through the hosted
WM file-bridge protocol (bridge request → P6 PPM frame + seq + `WmFsFrameReceipt`),
drives synthetic WM events, and records per-retained-frame timing; the perf lane
records the retained static-frame re-render distribution. Chrome capture reuses
`src/app/ui/chrome_showcase/main.spl` verbatim (the
`check-chrome-web-showcase-perf.shs` mechanism). No capture mechanism was invented
for this gate; the WM client is a build artifact composed from the repo's own shared
modules (`common.ui.wm_app_process_contract` wire format + the canonical Simple Web
renderer over `examples/06_io/ui/browser_common_elements_showcase.html`).

This report records retained-frame **evidence rows**: viewport, backend
requested/resolved, source revision, readback provenance, p50/p95, RSS, fallback
status, and checksum per row. It is not a frame-rate claim — every number below was
measured on the interpreter lane (see "Lane honesty" below) and proves the evidence
gate works end to end and reports fallback state honestly, not that any backend
meets a shipping perf target.

## Verdict

- status: **fail** (fail-closed by design: a GPU backend that resolves to a CPU lane
  is a FAIL of that backend's claim — see the metal row)
- reason: `metal:backend-fallback:metal->software`
- backends_checked: 4 (`software cpu_simd vulkan metal`)
- viewport: 320x240 (bounded for the interpreter lane; not a 4K/8K claim)
- retained_frames_per_row: 10 (perf lane); wm_events_per_row: 5 (WM lane)
- showcase_content: `examples/06_io/ui/browser_common_elements_showcase.html`
  (rendered from the filesystem; bridge `source_path` names the canonical showcase
  entry `examples/06_io/ui/web_standards_showcase_gui.spl`)
- source_revision: `3cbb169cc06b` (content-sha256 over the gate script, the showcase
  content/entry, the WM contract, and the Engine2D web renderer; override forbidden)
- simple_bin: `bin/release/aarch64-apple-darwin-macho/simple` (26,264,696 bytes,
  mtime 1788766698, identity self-hosted by content probe). Observed at runtime: it
  delegates compilation to an embedded `simple_seed` driver — the effective compiler
  lane is the Rust-seed codegen, which matters for the missing-extern rows below.

## Hosted WM retained rows (measured 2026-09-17, nearest-rank p50/p95)

| requested | backend resolved | fallback reason | readback source | frame p50 us | frame p95 us | WM round-trip p50 ms | WM round-trip p95 ms | max RSS KB | checksum | frame sha256 | status |
|---|---|---|---|---|---|---|---|---|---|---|---|
| software | software | none | cpu_mirror | 11223871 | 11286485 | 12198 | 13049 | 1488 | 329283806422413 | cac9e79c5a959110adf1db6469e60c429d3edb822c6f7ba947a7734ed5e48cde | ok |
| cpu_simd | cpu_simd | none | cpu_mirror | 11588947 | 11710583 | 12421 | 13448 | 0 (sampler missed; see notes) | 329283806422413 | cac9e79c5a959110adf1db6469e60c429d3edb822c6f7ba947a7734ed5e48cde | ok |
| vulkan | vulkan (probe ok) | none | unavailable | unavailable | unavailable | unavailable | unavailable | 0 | unavailable | unavailable | error |
| metal | **software** | **Metal SFFI not available** | cpu_mirror | 11222957 | 11394508 | 3225 | 11993 | 0 (sampler missed; see notes) | 329283806422413 | cac9e79c5a959110adf1db6469e60c429d3edb822c6f7ba947a7734ed5e48cde | fail (honest fallback) |

Row semantics:

- `frame p50/p95 us` — retained static-frame re-render cost distribution (10
  retained frames, per-frame `retained_us_*` samples in the perf driver log).
- `WM round-trip p50/p95 ms` — the WM-side event→frame-refresh latency: synthetic
  `WmFsAppEvent` written to the numbered event file until the seq file advanced
  (5 events per row, per-event samples in `wm.rt.samples`).
- `max RSS KB` — ps(1)-sampled maximum of the WM client process while it lived
  (macOS has no `/usr/bin/time -v`; provenance recorded, never substituted).
- `checksum` — canonical content checksum: the written PPM frame re-decoded with
  the repo decoder (`decode_ppm_to_argb`) and summed. Byte-for-byte identical
  (329283806422413) on every row that rendered, and equal to the frame produced by
  the canonical hosted client `web_standards_showcase_gui.spl` at the same
  viewport/backend (independently recomputed from its PPM in python during gate
  bring-up) — pixel-parity evidence between the gate's WM client and the existing
  showcase host.
- `frame sha256` — digest of the retained frame artifact (identical wherever the
  content rendered; the metal row carries the software-fallback frame's digest,
  labelled as such by `backend resolved`).
- Receipt correlation (software and cpu_simd rows): `event_seq=5`, `frame_seq=6`,
  wire checksum `1537909548` — five WM events consumed, six frames published
  (initial + 5 refreshes), receipt fields complete.

## Honest failures (recorded, not laundered)

- **metal → software** (`backend-fallback:metal->software`, probe reason
  `Metal SFFI not available`): the engine's own backend probe resolves metal to the
  software lane on this host, so the metal row FAILS with its timing recorded on the
  fallback lane. This is the bug record's required "fail honestly when Metal
  resolves to software" behaviour. The metal row's WM receipt carries
  `backend=software` — a fallback receipt, not a Metal claim.
- **vulkan error**: the backend probe resolves vulkan, but the deployed binary's
  vulkan route cannot run the gate's client program:
  `error: semantic: unknown extern function: rt_vulkan_copy_to_buffer_u32`
  (the same graph logs a `rt_vulkan_get_last_error` use-warning). The driver dies
  before the bridge; the row records error/wm-bridge-timeout with every timing field
  `unavailable` — nothing was fabricated. (During gate bring-up the same probe on a
  minimal program DID initialise a Vulkan device — backend_handle=5,
  device_identity=45344731160, readback tag `host_cache_after_device_copy` — so the
  device exists; the deployed binary's module surface is what is incomplete.)
- **cpu_simd / metal max RSS KB = 0**: the ps sampler started after the event loop in
  this run's script revision and the client had already exited; the 0 is recorded
  with provenance, not back-filled. The script now samples concurrently (fix applied
  2026-09-17 after this run); software's 1488 KB shows the sampler's real output.

## Chrome capture rows (sibling mechanism, all honest errors)

| backend | status | frame_source | backend_reported | verdict | detail |
|---|---|---|---|---|---|
| software | error | unknown | unknown | unknown | missing-receipt |
| cpu_simd | error | unknown | unknown | unknown | missing-receipt |
| vulkan | error | unknown | unknown | unknown | missing-receipt |
| metal | error | unknown | unknown | unknown | missing-receipt |

Root cause (from `build/wm-web2d-retained-perf-evidence/chrome_*/run.log`):
`[chrome-showcase] engine2d requested=... reported=...` logs the Engine2D resolve,
then `error: semantic: unknown extern function: spl_wffi_call_i64_into_bytes` — the
chrome dynlib ABI's real readback entry post-dates the deployed binary, so no
receipt is produced and the classifier's missing-receipt ERROR shape fires. This is
the same honest shape the sibling script uses (a missing receipt is ERROR, never a
pass); the gate now also aggregates the lane to `error` when every run checked
nothing (fix applied 2026-09-17).

## SimpleOS/QEMU row

- status: **skipped** (wired, non-blocking, per plan)
- reason: `run-not-requested:set-WM_WEB2D_RETAINED_PERF_RUN_SIMPLEOS=1`
- wiring: with the env set, the gate runs
  `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` under a bounded timeout
  (`WM_WEB2D_RETAINED_PERF_SIMPLEOS_TIMEOUT_SECS`, default 1200s) and records
  pass/skipped-with-reason without letting the row change the host-row verdict. A
  full QEMU row is not bounded enough for the shared host mid-session; the existing
  `simpleos_wm_fullscreen` evidence (`changed_bytes` only, no timing) remains the
  SimpleOS-side record until a dedicated run promotes it.

## Lane honesty (timing interpretation)

During this run the deployed lane ran with a JIT HIR fallback
(`Cannot infer field type: struct 'TextMetrics' field 'char_count'` → whole module
dropped to the interpreter, logged in the driver logs). The absolute frame numbers
(~11.2–11.7 seconds per retained 320x240 frame, ~12–13 s event→frame round trip)
are therefore interpreted-lane figures. They are recorded as
honest measurements of the current lane — not a native perf claim, and not
comparable to the 200 FPS / 4K retained contract owned by
`check-widget-showcase-4k-200fps.shs` (which requires the self-hosted release lane
and a validated baseline). The evidence claim of this report is narrower and
verifiable today: per-backend retained rows exist, flow through the real hosted-WM
file bridge, carry timing distributions, RSS, readback provenance, digests, and
fallback state — and they fail closed when a GPU backend is not what it claims.

## Evidence index

- gate script: `scripts/check/check-wm-web2d-retained-perf-evidence.shs`
- build dir: `build/wm-web2d-retained-perf-evidence`
- per-backend (software, cpu_simd, vulkan, metal):
  - `perf.driver.log`, `perf.samples`, `perf/perf.frame.ppm`
  - `wm.driver.log`, `wm.rt.samples`, `wm.rss`
  - `wm/wm.bridge`, `wm/wm.frame.ppm`, `wm/wm.frame.ppm.receipt`,
    `wm/wm.frame.ppm.seq`, `wm/wm.frame.ppm.timing`
- chrome lane: `chrome_<backend>/run.log`
- gate stdout transcript: `build/wm-web2d-retained-probe/full_run6.log`
