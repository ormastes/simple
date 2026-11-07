# CLI engine structured capture guard

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/engine_observer_capture_v1_spec.spl`.

Three authored scenarios, UNEXECUTED. ProcessResult fixtures exercise the helper used by the production observer after real structured capture; they do not qualify native execution or reap state.

| Case | Oracle |
|---|---|
| Baseline | Complete unsaturated info produces the existing stable identity; ordinary bounded stderr warning preserves prior behavior. |
| Authoritative flags | Valid JSON with exit0 is refused for output/stderr saturation, timeout, or inconsistent limit flags/type before info parsing. |
| Failure/bounds | Cancellation/nonzero status and overbound stdout/stderr cannot produce an observation. |

The production observer propagates capture Err and uses `process_run_bounded_observed_v1`. Policy, executable hashing and retained ownership paths are unchanged. No new process-result fields or native qualification are claimed.
