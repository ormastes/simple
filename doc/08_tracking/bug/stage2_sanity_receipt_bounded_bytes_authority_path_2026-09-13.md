# Site 14: every Stage-2 capability probe PASSES and the admission receipt still fails, on `bounded-bytes`

- **Status:** FIXED (2026-09-13, PR #800) — the verifier compared a padded `wc` string
- **Lane:** macOS `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`,
  virgin root, worktree `agent-aee4c61a47998a6a9`, carrying the site-13 fix
  (PR #800). Candidate built by that run:
  `.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple`,
  139,352,344 B, sha256
  `4ff156b78b97068ce722d0aef2496b645d60e3e7f27acf471e76dd4781b4982d`.
- **Severity:** the Stage-2 admission blocker that SUCCEEDS site 13
  (`stage2_cross_module_call_mangling_asymmetry_undefined_symbol_2026-09-13.md`).
  It is not caused by that fix — it was masked by it: the route failed before
  the receipt was ever published.

## The verdict

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
stage2-sanity-error: frontend-status role=p2_add failure=bounded-bytes
stage2-sanity-error: sanity-receipt role=bootstrap0 failure=status-verification
error: could not publish immutable Stage 2 admission receipt
exit:  4
FAIL — 1 check(s), stage stage2 failed (exit 4) with NO diagnostic text in any of 8 log(s)
```

## Everything the gate actually MEASURED passed

`stage3/aarch64-apple-darwin/stage2-receiver.log`, verbatim and complete:

```
Build complete: 1 compiled, 0 cached, 0 failed
bootstrap_stage2_struct_receiver=PASS
bootstrap_stage2_positional_stage3_route=PASS
```

Both capability probes PASS — including the positional Stage-3 route, which is
the step that failed to LINK in runs 24 and 25. In
`stage2-sanity.env.frontend-bootstrap-{0,1}.status.env`, **all four** frontend
probes report `raw_status=0` (`p2_add`, `stage2_mir_retention`,
`stage2_module_path_naming`, `hello_world_positional`) on **both** passes
(`SIMPLE_BOOTSTRAP=0` and `=1`). No probe failed. Only the receipt's
VERIFICATION of those probes failed.

## Root cause — BSD `wc -c` pads its output, and the comparison is a STRING compare

`scripts/check/lib/bootstrap-stage3/sanity.shs:297-298` (before the fix):

```sh
[ "$bootstrap_stage3_collector_bytes" = \
    "$(wc -c <"$bootstrap_stage3_probe_log_authority")" ] || \
    bootstrap_stage3_frontend_reject "$bootstrap_stage3_frontend_probe" bounded-bytes
```

Measured on this host:

```
$ printf '[%s]\n' "$(wc -c < /etc/hosts)"
[     213]
```

BSD/macOS `wc` right-pads its count to a fixed width even when reading from
stdin; GNU `wc` does not. So the left side is `653` and the right side is
`"     653"`, and `[ x = y ]` is a **string** comparison: false, for every probe,
on every macOS run — while the numbers themselves agree:

| value | source |
|---|---|
| `bytes_captured=653` | `stage2-sanity.env.frontend-bootstrap-0.log.bounded.env` |
| `653` | `wc -c` of `stage2-sanity.env.frontend-bootstrap-0.log` |

### Why the authority path is NOT the cause

An earlier draft of this record blamed `$CANDIDATE_FRONTEND_CAPTURE_PARENT` being
a directory file descriptor (`/dev/fd/6`, `candidate_frontend_admission.shs:104`)
that macOS cannot traverse. That is refuted by the script's own evidence:
`sanity.shs:241` hashes the SAME `$bootstrap_stage3_probe_log_authority` and
compares it to the recorded sha, and it runs EARLIER in the same loop iteration
and PASSED. The path resolves fine. Recorded here so the dead theory is not
re-derived.

### Why it appears only now

This is the first macOS run ever to REACH line 298. Runs 24 and 25 died inside
the candidate — SIGABRT in the SSA guard, then the site-13 link error — before
the admission receipt was verified at all.

## Fix

Normalise `wc`'s output arithmetically before comparing:

```sh
bootstrap_stage3_probe_log_actual_bytes=$(( $(wc -c <"$…authority") )) || return 1
[ "$bootstrap_stage3_collector_bytes" = "$bootstrap_stage3_probe_log_actual_bytes" ] || …
```

The byte equality is unchanged and still fails closed: a truncated or substituted
log still mismatches. Only the padding is removed. The check is NOT relaxed.

## Not attributable to the compiler

- The comparison is between a shell-side `wc -c` and a value written by the
  bounded-process collector. No compiler output participates.
- Every capability probe the candidate was asked to perform passed, including
  `bootstrap_stage2_positional_stage3_route=PASS`, which was red for the previous
  two runs.
- `scripts/check/check-bootstrap-stage2-sanity-gate.shs`, which drives the same
  `bootstrap_stage_sanity()` against **synthetic** candidate binaries (no compiler
  involved at all), is itself RED on this host on a different case:
  `FAIL — 30 case(s) checked, failures: operator_timeout_override_survives_scrub(...)`.
  That one is NOT fixed here and remains open.

Stage 3 and the full CLI were never reached on the run that found this, so there
is no Stage-3 artifact, no smoke-check result, and nothing was deployed.
