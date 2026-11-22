# slang image runner gate stays held if image generation panics

- **Status:** open. The return paths are fixed; a panic is not covered.
- **Found:** 2026-11-22, in a review of `serving_images.spl`.
- **Path:** `POST /v1/images/generations` → `serving_images.serve_images` →
  `sd_runner_try_acquire` → `_generate` (`sd_runner_open` / `sd_runner_run`) →
  `sd_runner_release`.

## What is fixed

`serve_images` now goes through `_generate_owned`, which calls
`defer sd_runner_release()` right after it takes the gate. The deferred release
runs after the tail call returns, not when the `defer` line is reached: probe
`C:/dev/slang-logs/mediafollow/probe/mf_defer2_spec.spl`, log `mf_defer2.log`
(the flag reads 1 inside the call and 0 after it). Every `return` out of the function releases it. Before this change the
function had one exit path and released the gate there, so no normal path
leaked. The change keeps that true when someone later adds an early return.

## What is still open

A panic leaves `SD_BUSY` set, for example an `unwrap` of an `Err` inside
`sd_runner_run` or a runtime fault in the shim call. Simple has no recover
construct, and `defer` does not run on a panic. This probe shows it:

- spec: `C:/dev/slang-logs/mediafollow/probe/mf_defer_spec.spl`
- log: `C:/dev/slang-logs/mediafollow/probe/mf_defer.log`. `defer` runs on an
  early return and on a normal return, but after `guarded(boom)` panics, the
  next example prints `FLAGAFTER=1`.

Impact: a server process that keeps running after a panicked request answers
every later image request with 503 `busy`. If a panic ends the process, the
gate goes with it and nothing leaks. Inside the spec runner, where each `it`
contains a panic, later examples would see the gate held.

## Fix direction

One of the following:

- a language-level `finally`, or `defer` that runs during panic unwinding;
- a request-level panic boundary in the HTTP server that runs the handler's
  cleanups;
- an owner token in the gate, so a supervisor can free a gate whose owner is
  gone. A timeout alone is not safe: it could let a second request close the
  context under a generation that is still running.
