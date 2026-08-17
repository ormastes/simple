# `SIMPLE_TIMEOUT_SECONDS` does not raise the light-daemon budget — specs report `daemon-no-response` instead of a verdict

- **Filed:** 2026-08-17
- **Status:** OPEN
- **Status:** CLOSED (2026-08-17)
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

## Resolution (2026-08-17) — CLOSED, but the earlier "fix" commit was docs-only

First, a correction to the record: **`5413bc94b01` landed no code.** Its
diffstat is two files, both under `doc/08_tracking/bug/`, +175 lines — it filed
this report and one other. Anyone reading "a fix was already committed" should
verify with `git show --stat` before trusting it. Re-checking the tree
confirmed the defect was fully intact: `effective_timeout_secs` read only
`run.timeout_secs`, `slow_it`, and `# @timeout_secs`, and a `grep` for
`SIMPLE_TIMEOUT_SECONDS` across `src/app/test_runner_new/` returned nothing.

Root cause: `parse_client_run` (`test_runner_client.spl`) initialised
`var timeout_secs = 120` as a hard literal, overwritten only by `--timeout` /
`--timeout=N`. Nothing on the path consulted the environment.

Fix location — the **default**, not `effective_timeout_secs`. `run.timeout_secs`
is the single value that feeds every downstream budget:
`light_request_timeout_ms_from_seconds(run.timeout_secs)` for the light-daemon
request, `run_one_direct`'s child `--timeout {child_timeout_secs}`, and the
per-path recompute at `effective_timeout_secs(p, run.timeout_secs)`. Defaulting
it at the parse site therefore fixes all of them at once, and preserves
precedence: explicit flag > environment > built-in 120.

The three helpers were then moved to a new
`src/app/test_runner_new/timeout_budget.spl`, because `test_runner_client.spl`
is a standalone script with a bare `fn main` — importing it into a spec trips
the documented fn-main collision that flips green specs to FAIL, so the logic
was untestable where it originally landed.

Hardening beyond the reported symptom: a malformed value now parses to 0 and
falls back to 120. Had it been parsed permissively, `SIMPLE_TIMEOUT_SECONDS=abc`
would have produced a 0-second budget that expires instantly and reports the
**entire suite** as timed out — strictly worse than the bug being fixed.

Reproducing spec, run reproduce-first by reverting
`client_default_timeout_secs` to its pre-fix body (return the constant
unconditionally), then restoring it:
`test/01_unit/app/test_runner_new/client_timeout_env_spec.spl`

```
before: Results: 4 total, 3 passed, 1 failed          (rc=1)
        ✗ honours SIMPLE_TIMEOUT_SECONDS when it is set
after:  Results: 4 total, 4 passed, 0 failed          (rc=0)
```

That spec is also the similar-problem detector: it covers the whole
**precedence ladder** rather than the single env read — default when unset, env
honoured when set, env re-read rather than cached, and each shape of malformed
value (`abc`, `800s`, `-5`, empty) falling back to 120 — plus the parser pinned
in isolation so a regression names itself.

Scope note for other lanes: the third rung (explicit `--timeout` beating the
environment) lives in `parse_client_run` and is not spec-covered, for the
fn-main reason above; it is structurally guaranteed by the flag branches
overwriting the default.

The remaining verdict-honesty gap is also closed in source. A client that gets
no daemon response cannot know that the spec executed, so it now emits
`executed=0 passed=0 failed=0 dropped=1 timeout=1 inconclusive=1` with
`reason=daemon-no-response`. Genuine worker and outer-bound timeouts continue
to use the red timeout verdict (`executed=1 failed=1`). The adjacent regression
pins both shapes so an infrastructure outage cannot be laundered into a failed
assertion, and a real worker timeout cannot be laundered into inconclusive.

**Impact on tonight's results:** any lane that set `SIMPLE_TIMEOUT_SECONDS`
instead of `--timeout` ran on a 120s budget. RED verdicts from those runs
carrying `reason=daemon-no-response budget_ms=120000` are false and must be
re-run before being believed. Verdicts with a real assertion failure (`✗` line)
are unaffected.

Commits: `7b85841e0e7` (fix), `a034851236d` (extraction + spec).
