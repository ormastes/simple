# Bootstrap sanity scrub loses outer session ownership

Retained run `stage2-893f6de5306-monitor-jobs10` compiled 899 units with zero
failures and linked the candidate, then failed at `running bootstrap compiler
sanity`. Its outer receipt records exit 90, escaped PID 8054, verified helper,
quiescent cleanup, and peak 2,584,672 KiB. The inner compilation receipt completed
successfully. PID 8054's command was not captured by the slower independent
process sampler, so its exact historical executable cannot be recovered.

The fresh sanity function unsets all exported variables, including the active
outer session ID, helper path and RSS policy. The subsequent bounded-log
collector therefore takes its standalone `setsid()` branch. The outer watchdog
correctly treats that child as escaped. The admitted-resume sanity function has
the same scrub. This mechanism is reproduced with the actual extracted sanity
prefix followed by the real bounded-log collector, without compiling anything.

Both functions now validate any present session pair before candidate execution
and retain exactly `SIMPLE_BOOTSTRAP_SESSION_ID`, `SIMPLE_BOOTSTRAP_SESSION_EXEC`
and `SIMPLE_BOOTSTRAP_RSS_CAP_MODE` through the scrub. Partial/empty contracts
fail with 125. Unrelated exported environment is still removed. No watchdog,
RSS threshold, session observation or identity cleanup logic changes.

## Evidence

Worktree `/Users/ormastes/simple-tmp/nested-session-contract-20260922`, files in
`build/native_probe/`:

| Focused run | Outcome | Wall time | time maximum RSS |
| --- | --- | ---: | ---: |
| sanity-session-before/profile.log | Exit 90, observed SID escape | 0.66 s | 47,775,744 bytes |
| sanity-session-final/profile.log | Fresh/resume same SID, setpgid collector, monitor retained, partial/empty rejected | 1.94 s | 47,775,744 bytes |

The after test executes both paths and negative cases; the before test stops
at its first failure. These paired profiles show fixture resource usage, not
compiler throughput or a production overhead comparison. The regression is
`test/01_unit/scripts/bootstrap_sanity_session_scrub_test.shs`.

`sanity-session-final/escape.env` confirms a real deliberate `setsid()` remains
rejected with exit 90 and quiescent=1. POSIX shell syntax and diff checks pass.
Independent Astra review covers the final production change.

The existing `check-bootstrap-stage2-sanity-gate.shs` test fails identically
before and after this change: its extracted harness does not initialize `os`,
and the production function reads it under nounset. Baseline diagnostic:
`fn.sh: line 138: os: unbound variable`. The baseline replay and changed logs
are retained under `sanity-session-final/`; this broader gate is not claimed
passing. This is an independent harness defect, not a passing negative test.

No SoSIX syscall changed. Prior session-specific SoSIX ENOSYS checks passed;
full existing SoSIX honesty test remains unverified because its alarm symbol
is absent, as recorded in the preceding monitor-mode report. No full bootstrap
was rerun, and the linked Stage2 candidate was not modified. The failed run is
not an admitted Stage2 receipt; reuse still requires provenance validation and
successful sanity/admission, without rewriting its original source identity.
