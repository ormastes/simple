# Production Simple Browser Performance and GC Budgets

> Source: `test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`

| Tests | Implemented | Explicit blockers |
|-------|-------------|-------------------|
| 7 | 1 | 6 |

This manual keeps unsupported production claims visible. The implemented
current-host slice binds the executable to `HOSTED_WM_ARTIFACT` and
`HOSTED_WM_ARTIFACT_SHA256`, starts its hidden renderer subprocess, obtains a
real frame, and verifies bounded process teardown. It does not claim RSS, GC,
10,000-cycle stability, unchanged-frame allocation avoidance, or Engine2D/font
lifecycle counts because those metrics are not exposed by the production
renderer today.

## Required admission inputs

- `HOSTED_WM_ARTIFACT`: admitted native `hosted_entry` executable.
- `HOSTED_WM_ARTIFACT_SHA256`: exact 64-character SHA-256 of that executable.

The scenario fails before launch when either input is missing or the digest
does not match. The canonical live-window evidence wrapper runs this focused
scenario after source-manifest and artifact admission; standalone environment
assertions are not artifact-admission evidence.

## Implemented scenario

### Close the admitted renderer subprocess within a bounded interval

1. Launch the admitted executable as the sandboxed browser renderer with a
   2,000 ms startup timeout.
2. Render a 64x48 static page with a 2,000 ms protocol timeout.
3. Record the renderer PID and confirm the subprocess is alive.
4. Close the renderer, allowing at most 10 seconds for the platform process
   teardown path.
5. Confirm the broker reports PID `0`, state `closed`, and the recorded PID is
   no longer alive.

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
- changed/unchanged frame and input-to-present percentiles;
- heap, RSS, browser-resource, and 10,000-cycle stability;
- GC pause, callback-queue, and post-cancel activity;
- Engine2D device/font/render-session/readback create-release counters;
- recorded-baseline comparison and five-percent regression gating.

Passing the bounded subprocess lifecycle scenario is not evidence for any of
those blocked claims.
