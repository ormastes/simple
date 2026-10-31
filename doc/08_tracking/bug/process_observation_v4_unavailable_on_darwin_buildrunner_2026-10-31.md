# BuildRunner worker cannot run on macOS: process observation V4 is Linux-only
## Open 2026-10-31

- Severity: blocks every BuildRunner task on macOS, including the Phase 2 BuildRunner Hello
  (`--memory-policy monitor`).
- `rt_process_observation_v4_capabilities_value` (`src/runtime/runtime_process_owned.c:3599`)
  reports `available=0, ENOTSUP` outside `#ifdef __linux__`. The darwin implementation exists only
  as `src/runtime/test/runtime_process_observation_v4_darwin_selfcheck.c`.
- The worker (`src/app/bootstrap_builder/worker.spl:171`) refuses before starting the compiler. It
  writes `worker.error` = `exact process observation V4 unavailable` and
  `compiler.not-started.sdn` (`SIMPLE-NO-CHILD-STARTED-1`). The manager reports
  `worker admission, resource or containment failure for hello` and exits 2.
- Measured 2026-10-31 with stage2 sha256 `adef5db249e4…` (Phase 3 rev8), runs `mon-1..4`. This is
  the same refusal recorded on 2026-10-29 (`real-buildrunner-monitor-20261029`).

## Needed
A darwin provider for process observation V4: exact child-tree start, wait, reap and kill proof
(kqueue `EVFILT_PROC` plus process-group retirement). Monitor policy does not waive this; it only
waives the memory cap.
