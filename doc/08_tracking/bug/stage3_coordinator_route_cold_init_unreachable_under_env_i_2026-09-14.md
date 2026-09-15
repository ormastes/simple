# Stage 3 coordinator route is unusable on a cold checkout: its own remedy cannot reach the child

- **Filed:** 2026-09-14
- **Status:** OPEN
- **Tree:** `origin/main` `4f4d0e12832`

## Symptom

Setting `SIMPLE_NATIVE_BUILD_THREADS=5` switches the Stage 3 resume to
`requested_route=coordinator`. On a checkout that has never built, it fails in
under two minutes with a one-line log:

```
SCV-E-ADMISSION: compile-event-journal-missing (first build in this checkout:
                 rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)
```

Re-running with `SIMPLE_SCV_INVENTORY_COLD_INIT=1` exported produces the
**identical** failure.

## Why the remedy cannot work

`scripts/bootstrap/resume-stage3-from-admitted.sh` states it twice in its own
comments (lines 577 and 603): the Stage 3 child runs under `env -i`, so an
outer variable never reaches it. Only variables the script explicitly bakes
into the invocation are forwarded — `SIMPLE_NATIVE_BUILD_THREADS` is one,
`SIMPLE_SCV_INVENTORY_COLD_INIT` is not.

So the error prescribes a fix that the script makes unreachable. The
coordinator route is therefore unusable on a cold checkout, and the
multi-threaded Stage 3 path is closed, by any means available to an operator.

## Second finding: the declared fallback never fires

Both failing runs recorded `requested_route=coordinator fallback_route=direct`
and then failed outright. The declared `direct` fallback did not engage. A
fallback that is recorded but never taken is worth a separate look.

## Not fixed here

Two candidate fixes — adding the variable to the forwarded allowlist, or having
the script cold-initialise the journal itself when it is missing — are both
behaviour changes to an admission-bearing script and were not made
speculatively. Measured on macOS arm64 (`hw.ncpu=10`), F74 round 3.
