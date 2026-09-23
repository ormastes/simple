# Windows Stage 2 frontend Job wait after root exit

At exact source HEAD `c3eee18b5ef200e6ea1c454b2c24c5331e4ff558`, the
full Stage 2 replay in `build/review/stage2-hir-replay-c3eee18-msvcenv.receipt`
finished with outer status 2 because frontend admission rejected the candidate.
The linked Stage 2 compiler completed 900/900. The positional hello-world
native build reported link success at 22.236 seconds, but its inner bounded
collector returned timeout status 124 at the 180-second limit. The outer
receipt reports `raw_status=2`; the matching log records the inner 124 and
the 22.236-second link. This is an approximately 158-second post-link wait,
not a measured memory or RSS problem.

The Windows collector defaults to `wait-job`. A synchronous compiler root can
exit after linking while a contained helper still holds the output pipe open.
The collector then waits for every Job member until the timeout. The identity
of the remaining member in this replay was not captured, so it must not be
attributed to a specific tool or telemetry process.

Frontend native-build probes now request `terminate-job` on Windows and bind
that policy to the collector receipt. The collector records the root-exit
elapsed time, active count, and at most 16 member PIDs with image basenames
before termination. These diagnostics are advisory and contain no command
lines, environment values, or image directories. `job_remnants_terminated`
continues to mean root-exit-policy cleanup only; timeout and overflow also
terminate the Job but leave this flag `no`. Root exit status, log bounds and
hash, and the fresh executable execution and expected stdout gates still
decide admission. A successful root plus an incomplete artifact still fails.

Focused regression: `test/01_unit/scripts/process_group_bounded_log_windows_test.py`
exercises real Job orphan success/failure, live-root timeout, overflow, and
bounded diagnostics. `test/01_unit/scripts/candidate_frontend_windows_job_policy_test.shs`
checks frontend option propagation and receipt binding. A full bootstrap
replay remains necessary to establish whether this specific candidate can
pass the complete admission after the policy change.
