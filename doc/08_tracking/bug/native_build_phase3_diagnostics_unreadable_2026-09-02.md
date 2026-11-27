# `native-build` of a hello world fails in phase 3 with its diagnostics lost in transport

- **Filed:** 2026-09-02
- **Status:** FIXED (bc5abc26ce0, PR #320; gate check-phase3-diagnostics-reported.shs)
- **Severity:** P1 — the build fails AND destroys the evidence of why, so the
  failure cannot be triaged from its own output
- **Component:** seed `native-build` worker / diagnostic transport
- **Found by:** the bug-DB triage lane, while closing
  `export_use_wildcard_rejected_but_used_1719_times_2026-08-17.md`

## Symptom

On a seed built from `origin/main` `1b76db1d6c3` (aarch64-apple-darwin), the
two-line hello world from the record above:

```
$ printf 'fun main()\n  print("hi42")\n' > hw.spl
$ <fresh-seed> native-build hw.spl -o /tmp/hw.bin
...
[ERROR] phase 3 FAILED
[build] hir unknown/unknown step 2/6 +6208ms dt=77ms failed
[ERROR] phase 3 FAILED (diagnostics unreadable: error array did not survive transport)
error: native-build worker exited with code 1.
RC=1
```

Repeated three times as `error: native-build failed without diagnostics`.

## Why this is filed separately

It is the residual failure left after the `export use X.*` row was closed. That
row claimed the build was blocked by a rejected `export use` form; measurement
showed that diagnostic is now a WARNING (75 of them are printed and the
pipeline walks past all of them) and the build dies later, here. Leaving this
attached to that row would keep a fixed diagnostic looking live and hide a
distinct defect behind it.

## What makes it worse than an ordinary build failure

The message is explicit that the error array "did not survive transport": the
worker knows it failed and knows it cannot say why. Every downstream consumer —
a gate reading a verdict, a person reading a log — gets a build failure with no
cause. The phase and step are named (`hir`, step 2/6), so the transport, not
the detection, is the missing half.

## Not established

- Whether the underlying phase-3 error is itself a real defect or a
  configuration gap on this host.
- Whether the transport loss is specific to the worker path or also affects
  in-process builds.
- Whether other platforms reproduce; only aarch64-apple-darwin was measured.

## First thing to do

Make the worker fail LOUD before fixing whatever phase 3 is unhappy about — a
build that cannot report its own errors will hide the next defect too.

**Revalidated 2026-11-02: still plausible because the report title (`native-build` of a hello world fails in phase 3 with its diagnostics lost in t) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Lane note 2026-11-03 (wl01 lane)
Deferred: reproduction needs native-build phase 3 output transport, not runnable on this lane (seed lacks entry-closure native-build).

**Closed 2026-11-03 (already fixed):** `bc5abc26ce0` (#320) retired the
unconditional "diagnostics unreadable" line in
`src/compiler/80.driver/driver_stage_hir_v1.spl` (`stage_lower_hir_failure_v1`).
It now reads `ctx.error_message_at(i)` through the `rt_heap_ref_wellformed`-guarded
accessor and logs each surviving message verbatim (cap 20, plus a "further N"
line); the "no readable diagnostics" line prints only when nothing survives. The
string no longer exists in `src/`. Regression gate:
`scripts/check/check-phase3-diagnostics-reported.shs` (asserts the specific HIR
error text appears and the old wording does not).
