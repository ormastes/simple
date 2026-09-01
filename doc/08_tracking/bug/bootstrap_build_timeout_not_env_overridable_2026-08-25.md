# Bootstrap compiler-budget timeouts were not env-overridable — load-sensitive false negative in Stage 2 admission (2026-08-25)

- **Status:** FIXED (2026-08-25)
- **Severity:** high — rejects a *good* Stage 2 trust root, so the whole
  Stage 2 → Stage 3 → Stage 4 self-host chain is unreachable on a loaded host.
- **Area:** bootstrap wrapper / redeploy-gate candidate admission
- **Guard:** `scripts/check/check-bootstrap-timeout-env-overridable.shs`

## Symptom

On a pinned clean worktree at `origin/main e8db788629b`, Stage 2 **built
cleanly**:

```
Build complete: 757 compiled, 0 cached, 0 failed      (28409 KB linked)
```

and was then **rejected by the wrapper's sanity gate**:

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.0-RC \
    unsupported_status=1 frontend_status=1 candidate_unchanged=true
```

The candidate was preserved as
`stage2/x86_64-unknown-linux-gnu/simple.rejected`, the wrapper exited 1, and the
failure-diagnosis helper reported `UNDIAGNOSABLE: the stage failed with no error
message of any kind`.

## Evidence that the candidate was good

Replaying the *exact* smoke by hand against the preserved `simple.rejected` —
the `candidate_frontend_smoke` argv from
`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`:

```
native-build --backend cranelift --runtime-bundle core-c-bootstrap \
  --entry-closure --entry scripts/check/cert/redeploy_gate/fixtures/p2_add.spl
```

**succeeds**: exit 0, `Build complete: 1 compiled, 0 cached, 0 failed`, 39 KB
binary, **8.5 s** wall.

## Root cause

`candidate_frontend_admission.shs` itself is written to honour the environment
(lines 3-6):

```sh
COMPILER_PROBE_TIMEOUT_SECONDS=${COMPILER_PROBE_TIMEOUT_SECONDS:-5}
COMPILER_BUILD_TIMEOUT_SECONDS=${COMPILER_BUILD_TIMEOUT_SECONDS:-60}
COMPILER_EXEC_TIMEOUT_SECONDS=${COMPILER_EXEC_TIMEOUT_SECONDS:-5}
COMPILER_CHECK_KILL_GRACE_SECONDS=${COMPILER_CHECK_KILL_GRACE_SECONDS:-1}
```

but **every caller overwrote it unconditionally immediately before sourcing
it**:

| site | lines |
|---|---|
| `scripts/bootstrap/bootstrap-from-scratch.sh` | 1102-1105 |
| `scripts/bootstrap/resume-stage3-from-admitted.sh` | 313-316 |
| `scripts/check/lib/bootstrap-stage3/sanity.shs` | 369-372 (command-prefix form) |

So the operator-facing knob was dead: exporting
`COMPILER_BUILD_TIMEOUT_SECONDS` had no effect whatsoever.

A 60 s budget is not survivable on this host at load ~39 with three concurrent
agent lanes — the same work that takes 8.5 s idle exceeds 60 s under
contention. The gate is therefore a **load-sensitive false negative**: it
reports a product defect where none exists, and there was no supported way to
widen it.

Second-order defect (not fixed here, filed as follow-up below): the sanity
failure path discards the smoke's captured stderr, which is why the diagnosis
helper could only say `UNDIAGNOSABLE`.

## Fix

All four knobs at all three caller sites converted to the `${VAR:-default}`
form, keeping the historical defaults (5 / 60 / 5 / 1) so unset behaviour is
byte-identical. No default was changed and no gate was weakened: a too-small
budget still fails closed.

## Guard

`scripts/check/check-bootstrap-timeout-env-overridable.shs` proves three
properties by *executing* the real assignment lines out of the real files
(behaviour, not a text pattern), plus one live probe:

- (a) unset → the historical default,
- (b) an exported value is honoured,
- (c) a deliberately tiny budget (1 s vs a 30 s stub candidate) still makes
  `candidate_frontend_smoke` FAIL, and fails promptly — so "honours the env"
  cannot be satisfied by ignoring the budget altogether.

Verdict convention: last stdout line `PASS — …` exit 0 / `FAIL — …` exit 1 /
`ERROR — nothing was checked` exit 2; a scan that made zero assertions or found
zero sites is ERROR, never a pass. `--selftest` runs before every scan and is
fatal (5 fixtures: correct form must pass; the incident's exact unconditional
`=60` must FAIL naming the clobber; a drifted default must FAIL; the
command-prefix-with-continuation form must parse and pass; a file with no knobs
must contribute zero assertions so the caller is forced to ERROR).

Measured after the fix:
`PASS — 17 assertion(s) across 4 site(s), 0 offenders`.
Negative control on the real tree (one site reverted to `=60`):
`FAIL — 17 assertion(s) across 4 site(s), 1 offender(s)`.

## Follow-up (open)

- The Stage 2/3 sanity failure path should print the smoke's captured stderr
  instead of reporting `UNDIAGNOSABLE`. A gate that can reject a good candidate
  and then say nothing about why cost a full session of investigation here.
