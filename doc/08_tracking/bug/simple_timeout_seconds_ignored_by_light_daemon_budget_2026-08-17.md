# `SIMPLE_TIMEOUT_SECONDS` does not raise the light-daemon budget — specs report `daemon-no-response` instead of a verdict

- **Filed:** 2026-08-17
- **Status:** OPEN
- **Severity:** high for tooling/CI honesty (produces INCONCLUSIVE runs that read as failures)
- **Component:** `src/app/test_runner_new/test_runner_client.spl`,
  `src/app/test_daemon/light_protocol.spl`

## Symptom

Running a spec with a generous `SIMPLE_TIMEOUT_SECONDS` still dies at 120s:

```
$ SIMPLE_TIMEOUT_SECONDS=840 timeout 900 bin/simple test \
    test/00_formal_verification/compiler/lean_basic_spec.spl

ERROR: test daemon timed out: .../lean_basic_spec.spl
ERROR: no response from the light daemon within 120000ms + 2000ms grace.
SPEC FILE VERDICT: ... passed=0 failed=1 timeout=1 reason=daemon-no-response budget_ms=120000
```

Note `budget_ms=120000` despite the env var asking for 840s.

The same spec, same machine, with the **CLI flag** instead:

```
$ timeout 900 bin/simple test \
    test/00_formal_verification/compiler/lean_basic_spec.spl --timeout 800

Results: 4 total, 4 passed, 0 failed
```

Confirmed on a second spec: `lean_workflow_spec` reported
`NO-RESULTS-LINE(INCONCLUSIVE)` under `SIMPLE_TIMEOUT_SECONDS=840` and
`9 total, 9 passed, 0 failed` under `--timeout 800`.

## Why this matters more than an ordinary timeout

The failure is **reported as a spec failure**: `failed=1`, exit 1, and a
`SPEC FILE VERDICT` line claiming the spec failed. It is not a spec failure —
the spec passes. An agent or CI lane sweeping a tree with
`SIMPLE_TIMEOUT_SECONDS` set (which is the documented idiom, and what
`.claude/rules/` examples use) will silently record healthy specs as RED, or
churn re-running them at ever-larger env values that can never take effect.

During this sweep, **6 of 17** `test/00_formal_verification` specs were
initially recorded this way. Five of the six are fully green once the budget
actually applies.

## Mechanism

`run_one_via_daemon(path, timeout_ms, seq)`
(`test_runner_client.spl:403`) takes its budget from

```
val p_timeout_ms = light_request_timeout_ms_from_seconds(
    effective_timeout_secs(p, run.timeout_secs))     # line 639
```

`run.timeout_secs` is the **CLI `--timeout` value**.
`effective_timeout_secs` (line 320) only ever raises it from two other
sources — a `slow_it ` occurrence (floor 600) and a
`# @timeout_secs <N>` header directive — and consults no environment at all.
`light_request_timeout_ms_from_seconds` (`light_protocol.spl:20`) then just
scales seconds to ms, clamped to `LIGHT_REQUEST_MAX_TIMEOUT_MS = 2400000`.

So there is no path by which `SIMPLE_TIMEOUT_SECONDS` reaches the daemon
budget. The env var does still fire elsewhere — `test_runner_client.spl:176`
explicitly says "the override still fires" when discussing the debug-seed
shadowing bug — which is precisely what makes this confusing: the variable is
real and honoured on the *other* timeout path, just not this one.

## Workarounds available today

- Pass `--timeout <secs>` on the CLI (verified to work).
- Add a `# @timeout_secs <N>` header directive to a spec that genuinely needs
  longer.

## Fix direction

Either have `effective_timeout_secs` read `SIMPLE_TIMEOUT_SECONDS` as a floor,
or — if the env var is deliberately scoped to the non-daemon path — make the
daemon-timeout error say so explicitly, e.g. *"budget comes from `--timeout` /
`# @timeout_secs`; `SIMPLE_TIMEOUT_SECONDS` does not apply here"*. The current
message instead suggests `rm -rf .build/test_daemon_light`, pointing at a stale
lock that is usually not the cause: during this incident the daemon was alive
and serving other specs normally (its `responses/` dir was being written
throughout), and 0 of the 17 pass-1 logs showed a wedge.

## Repro

```
SIMPLE_TIMEOUT_SECONDS=840 bin/simple test test/00_formal_verification/compiler/lean_basic_spec.spl   # daemon-no-response, budget_ms=120000
bin/simple test test/00_formal_verification/compiler/lean_basic_spec.spl --timeout 800                # 4 passed
```
