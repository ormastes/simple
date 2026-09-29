# Nested bootstrap guard and temporary RSS monitoring

The retained Stage2 run at source 89e71c6a33d failed before compiler execution:
`new session refuses inherited session contract`, exit 89. Both the Stage2/3
transcribed launcher and Stage4 native launcher requested a new session even
when a whole-bootstrap guard already owned the session.

The launchers now request strict inheritance when either session variable is
present. The watchdog continues validating admission, helper hash and actual
SID. Partial and spoofed contracts fail before workload execution. Otherwise a
new session is created. An outer enforcing guard still samples the whole tree,
including the Rust phase and nested monitors; inner guards sample their subtree.

## Temporary monitor mode

Explicitly set `SIMPLE_BOOTSTRAP_RSS_CAP_MODE=monitor` for the diagnostic build,
or pass `--rss-cap-mode=monitor` to the outer watchdog. The validated policy is
forwarded across the Stage2/3 hermetic environment and to nested timeout guards.
Monitor mode disables only the two RSS threshold kill decisions. Session/PID
identity, sampling, observer failures, timeout and cleanup remain enforced.
Receipts record `rss_cap_enforced=0` and `rss_limit_kib=unlimited` alongside the
configured threshold (`max_rss_kib`), peak RSS and sample timing. A monitor run
is not evidence of an admitted under-limit bootstrap.

Default mode is `enforce`, decimal 6 GB (5,859,375 KiB), sampled rather than a
kernel hard limit. For final verification explicitly set
`SIMPLE_BOOTSTRAP_RSS_CAP_MODE=enforce` and pass `--rss-cap-mode=enforce` to the
outer watchdog with `--max-rss-kib=5859375`. Keep that outer guard around the
entire canonical bootstrap, including Rust. No full bootstrap was rerun here.

## Focused evidence

Worktree: `/Users/ormastes/simple-tmp/nested-session-contract-20260922`.
Evidence is retained under `build/native_probe/` in that worktree.

- `nested-guard-before/profile.log`: same launcher fixture fails exit 89 before
  fix; 1.02 s, 47,742,976 bytes maximum RSS reported by macOS time.
- `nested-guard-final/profile.log`: PASS nested/standalone SID, admission,
  partial/spoof rejection, cap cleanup and exit propagation; 3.54 s,
  271,958,016 bytes (includes intentional 128 MiB allocation cap fixture).
- `rss-monitor-final/profile.log`: PASS monitor threshold, default enforcement,
  invalid policy, timeout/grace, observer tamper, real Stage2/3 env-i propagation;
  5.14 s, 47,742,976 bytes.
- `stage4-monitor/`: actual extracted Stage4 launcher under outer monitor with
  1 KiB configured threshold completes in inherited session, enforced=0.
- Existing bootstrap session transcript and PID/PGID identity unit tests PASS.
- Independent Astra review approved production changes and both focused suites.

Paired identical `sleep 1` workload profiles under `rss-mode-pair/`:

| Policy | Wall seconds | User/system seconds | time maximum RSS bytes | Sampled tree peak KiB |
| --- | ---: | --- | ---: | ---: |
| enforce | 1.56 | 0.16 / 0.21 | 47,742,976 | 2,464 |
| monitor | 1.43 | 0.16 / 0.22 | 47,562,752 | 2,512 |

These are single focused fixture measurements, not compiler throughput or
production bootstrap overhead claims. Startup helper compilation contributes
to time/RSS. The before/after full tests execute different numbers of cases.

POSIX shell syntax checks pass; no platform syscall implementation changed.
The existing SoSIX `simpleos_process_session_honesty_test.c` cannot link because
`simpleos_test_alarm` is absent in this source revision. A temporary copy omitting
only its two alarm assertions passes actual session/identity ENOSYS and sleep
checks. Full SoSIX execution remains unverified; no success is claimed for the
unaltered full fixture.
