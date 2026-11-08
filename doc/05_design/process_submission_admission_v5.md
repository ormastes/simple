# Unix submission expiry at the retained process owner

`ProcessObservationReservationV4.start_admitted(request, expires_at_unix_ms)`
adds final submission admission without changing the existing reservation,
V4 observation/acknowledgment protocol, request wire format, environment,
executable/cwd pin behavior or workload `wall_budget_ns` lifetime. The native
symbol is `rt_process_observation_v5_reserved_start_admitted_value`.

The caller first verifies the real launch/control grant and supplies the
minimum applicable positive Unix-millisecond expiry. This number is data, not
authority by itself. The native owner consumes the attempt and binds its
deadline once. Duplicate starts cannot update it. Missing/nonpositive deadlines,
unknown or invalid Unix clock values and `now >= expiry` refuse admission.

The owner checks the actual realtime clock before preparation and again after
preparation immediately before Linux `fork` or Darwin `posix_spawn`. A refusal
before child creation consumes the attempt into the existing NoChild state;
the reservation remains caller-owned until confirmation. Clock-query failure
uses `EIO`, expiry uses `ETIMEDOUT`, invalid deadline uses `EINVAL`. The nullable
receipt allocation cannot erase reservation authority or these retained scalar
admission errors.

Linux checks again immediately before `fexecve`. Darwin checks again before
resuming its actual suspended child. A refusal at either point occurs after a
child was created: it follows the existing owned cleanup/reap path, never a
fabricated NoChild state. Observe/retire, frozen acknowledgment and confirmation
continue through the same retained owner. Once execution is admitted, the
grant expiry does not stop the workload; its existing execution/cleanup budget
remains authoritative.

The legacy `start` route supplies no submission deadline and performs no new
realtime clock queries. Unsupported native platforms, including the existing
Windows V4-unavailable branch, return explicit unsupported; no weaker provider
or second supervisor is introduced.
The reservation API remains parent-coordinator-only. This change does not add
an origin fence to the existing process-global reservation mutex/registry and
does not make reservation calls from a forked Simple worker safe. The Linux
native child performs only the local clock check before exec, without invoking
the reservation API or acquiring its mutex.

## Verification boundary

The standalone clock mechanism test compiled and ran once successfully with
explicit BFD linking after an approved changed-harness retry. The first default
Mold attempt failed because its 8 GiB virtual reservation exceeded the initial
64 MiB child address-space cap; that was a harness/resource failure, not a
process-owner result. Exact source/compiler/binary/log hashes and both attempts
are retained under `doc/09_report/process_submission_admission_v5_clock_20261107/`.
The successful attempt used the separately approved 2 GiB address-space cap,
128 MiB aggregate RSS watchdog, CPUs 0–4 and 30/5 second compile/run limits.
This is **clock-mechanism PASS only**. Every owner ABI, spawn, exec, reap and
Simple integration fixture remains **NOT_RUN**; no broader build was authorized.

The Simple integration spec exercises actual reservation entry, consumed
expired/missing-deadline refusal and replay prevention. The C clock mechanism
selfcheck covers the exact expiry boundary, unknown clock, invalid clock and
legacy no-clock-query behavior through a test-only syscall substitution.
These controls are not proof of final-create or post-create child cleanup.
The live Darwin fixture adds final-spawn expiry/unknown-clock and post-spawn
expiry controls using the same actual owner and child. The authored Linux
fixture `runtime_process_submission_admission_v5_linux_selfcheck.c` uses an
actual sealed memfd executable snapshot and real fork/ptrace/exec/observe/reap
with a small value-runtime and duplicate-pin test bridge. Its clock/fork
wrappers exist only in the test translation unit. It checks zero child
creation for final-fork expiry/unknown clock, retained actual ownership for
post-fork/pre-exec expiry, and a positive actual-exec stdout marker. Both live
fixtures remain **NOT_RUN**. No successful child execution or cleanup is
inferred from their source or the clock-mechanism result.
