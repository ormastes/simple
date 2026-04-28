# Watchdog kill — llm_math_system_spec 120 s budget exceeded — 2026-04-28

Cross-ref: `.sstack/fix-perf-bugs/timeout_triage.md` (kill #25, line 9041).

## TL;DR

`test/system/llm/llm_math_system_spec.spl` hit the watchdog at the 120 s
boundary, immediately preceded on stderr by:

```
error: rt_cli_watch_file is not supported in interpreter mode
```

The triage hypothesised the spec was polling on the unsupported FFI in a
loop. **That hypothesis is wrong.** Investigation:

1. The spec **does not call** `cli_watch_file` or `rt_cli_watch_file`
   anywhere. Its sole external is `rt_process_run("claude", args)`.
   The unsupported-FFI error in stderr came from a DIFFERENT spec
   running in the same `--only-slow` worker just before — most likely
   `test/sffi/sffi_public_api_spec.spl` or
   `test/unit/app/io/cli_ops_handlers_spec.spl` (the only callers of
   `cli_watch_file`).
2. The real workload: 2 × `claude --output-format json --model haiku`
   subprocess invocations via `rt_process_run`. Each call hits the
   live Anthropic API.
3. Observed today in isolation: spec passes in **26 359 ms** when the
   API responds promptly. Under rate-limiting / network latency, two
   live API round-trips can easily exceed the 120 s slow-bucket
   timeout — that is what the `--only-slow` run hit.

## Symptom (slow_run only)

```
error: rt_cli_watch_file is not supported in interpreter mode
[watchdog] wall-clock timeout (120s) exceeded
[watchdog] crash report: .simple/logs/crash_3709914.log
```

Triage attribution: `test/system/llm/llm_math_system_spec.spl` (heuristic,
based on stderr proximity).

## Reproduction

```bash
$ timeout 30 bin/simple test test/system/llm/llm_math_system_spec.spl
... PASSED (26 359 ms) — 2 examples, 0 failures
```

Reproduces as a hang only when:
- `claude` CLI is slow to respond (>60 s/call), OR
- `claude` CLI is missing on PATH and falls into a long error-path, OR
- The Anthropic API is rate-limiting / 5xx-ing.

## Root-cause class

**Genuinely-slow workload** + **cross-spec stderr-noise misattribution**.

The spec is a *live* system test — every `it` block makes a real network
call. There is no infinite loop, no unsupported-FFI poll, no logic bug.
The 120 s budget is just too tight for two live LLM round-trips when the
API is loaded.

## Proposed fix shape

1. **Bump the bucket / tag the spec.** Add `# tag: live-network, slow-120s`
   (or wrap in a `@network` skip-by-default group) and request a 300 s
   wall-clock budget for `--only-slow` runs that include `live-network`.
2. **Skip when claude binary missing.** Add an early
   `if not have_binary("claude"): return skip("claude CLI not on PATH")`
   guard so missing-tool environments fail fast instead of waiting on a
   60 s subprocess error path.
3. **Investigate the real source of `rt_cli_watch_file is not supported in
   interpreter mode`** — this is from `cli_watch_file` being called via
   `test/sffi/sffi_public_api_spec.spl` (`AC-3: cli_watch_file returns a
   handle for a valid path`). The Rust runtime extern is intentionally
   not implemented in interpreter mode. Either:
   - Implement `rt_cli_watch_file` as an interpreter-mode no-op that
     returns `-1` (clean error), OR
   - Mark the SFFI spec as `# tag: only-compiled` so the interpreter
     run skips it.

## Workaround

For local development, run the spec only in the dedicated live-LLM
bucket; do not include in the default `--only-slow` sweep.

## Status

OPEN — pending tag/budget update on `llm_math_system_spec.spl` and a
separate decision on `cli_watch_file` interpreter-mode behaviour.
