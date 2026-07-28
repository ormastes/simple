# Production Simple Browser Performance and GC Budgets

> Source: `test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`

| Tests | Implemented | Explicit blockers |
|-------|-------------|-------------------|
| 8 | 2 | 6 |

This manual keeps unsupported production claims visible. The implemented
current-host slices bind the executable to `HOSTED_WM_ARTIFACT` and
`HOSTED_WM_ARTIFACT_SHA256`, runs 32 sequential hidden renderer subprocesses,
obtains a real frame from each, verifies bounded process teardown, and records
one accepted-input-to-completed-present interval on the real hosted winit path.
It does not claim an input p95, FPS, 60-minute RSS, GC, 10,000-cycle stability,
unchanged-frame allocation avoidance, or Engine2D/font lifecycle counts.

## Required admission inputs

- `HOSTED_WM_ARTIFACT`: admitted native `hosted_entry` executable.
- `HOSTED_WM_ARTIFACT_SHA256`: exact 64-character SHA-256 of that executable.

The scenario fails before launch when either input is missing or the digest
does not match. The canonical live-window evidence wrapper runs this focused
scenario after source-manifest and artifact admission; standalone environment
assertions are not artifact-admission evidence.
Its evidence receipt records
`linux_hosted_wm_live_window_browser_lifecycle_cycle_count=32` only after the
focused scenario succeeds.

## Implemented scenario

### Record one admitted input-to-present sample within 50 ms

1. On platform event ingress, capture a positive monotonic `input_received_us`;
   retain it only when that event is semantically accepted, bound to its
   `event_id` and `mutation_revision`.
2. Immediately after `hosted_winit_present_pure_simple_pixels` reports a
   successful native present, record `present_completed_us`, the real winit
   `present_count`, and compositor `skipped_frame_count`.
3. Require `input_to_present_us` to equal the monotonic timestamp difference,
   be positive, and be at most 50,000 microseconds.
4. Require the snapshot render event/revision to equal the input receipt and
   run the focused perf scenario against the same admitted artifact digest.

This is one current-host sample. It is not NFR-WEB-BROWSER-004 p95 evidence and
does not cover every required input class.

### Close 32 admitted renderer subprocesses within bounded intervals

1. For generations 61 through 92, launch the admitted executable as a new
   sandboxed browser renderer with a 2,000 ms startup timeout.
2. Render a 64x48 static page with a 2,000 ms protocol timeout in each process.
3. Record each renderer PID and confirm the subprocess is alive.
4. Before close, read `VmRSS` and `VmHWM` directly from `/proc` for the current
   test/browser host PID and renderer PID. Require positive values, distinct
   PIDs, and each high-water mark to be at least its current RSS.
5. Track the largest sampled combined RSS and the largest sum of the two
   per-process high-water marks. The latter is named
   `combined_peak_upper_bound_max_kib`: the peaks may occur at different times,
   so it is a conservative upper bound rather than a measured simultaneous
   peak. Require both values to remain at or below 393,216 KiB.
6. Close each renderer before starting the next, allowing at most 10 seconds
   for the platform process teardown path.
7. After every close, confirm the broker reports PID `0`, state `closed`, and
   the recorded PID is no longer alive.
8. Recheck all 32 recorded PIDs after the loop and require a final completed
   cycle count of exactly 32.
9. Record both RSS values in the focused spec log.

Evidence captures: executed binary, subprocess log, and artifact identity.

## Supplemental current-host receipt

The canonical Linux live-window wrapper records one unchanged-frame work-
avoidance sample after the restore frame. It issues a snapshot-only command,
which does not mark the production compositor dirty, and requires the retained
render revision, frame checksum, backend, readback source, backend handle, and
captured pixels to remain identical. The receipt is
`linux_hosted_wm_live_window_unchanged_frame_status=pass`, bound to the same
admitted native artifact and source manifest as the other wrapper evidence.

This is a single current-host retained-frame observation. It is not an
allocation count, frame-time percentile, RSS plateau, GC measurement, or soak.

## Explicit blockers

The following scenarios intentionally fail until their named production metrics
and receipts exist:

- warm/cold startup, first-render, and navigation percentiles;
- changed/unchanged frame percentiles and input-to-present p95 across every
  required input class;
- 60-minute heap/RSS, browser-resource, and 10,000-cycle stability;
- GC pause, callback-queue, and post-cancel activity;
- Engine2D device/font/render-session/readback create-release counters;
- recorded-baseline comparison and five-percent regression gating.

Passing the bounded repeated subprocess lifecycle scenario proves only process
handle reclamation and a short-cycle Linux RSS ceiling across 32 sequential
cycles. NFR-WEB-BROWSER-005 remains blocked because it requires browser plus
renderer RSS after 60 minutes; this scenario is not that duration. It is not
evidence for any other blocked claim, including GC behavior.
