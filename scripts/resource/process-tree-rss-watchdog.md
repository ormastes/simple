# Sampled bootstrap RSS guard

`perl scripts/resource/process-tree-rss-watchdog.pl --max-rss-kib=5859375
--interval-ms=100 --timeout-seconds=660 --receipt=/absolute/run.rss.env
-- COMMAND ARGS...` supervises one command on macOS/Linux. The production
default and absolute configuration ceiling are decimal 6 GB (5,859,375 KiB).
Overrides may lower it, and all larger CLI/environment values are rejected
before installation or workload launch. The ordinary compilation
acceptance target remains **less than 1,000,000,000 bytes** (at most 976,562
whole KiB), assessed separately from the emergency guard threshold.

Before workload launch the guard compiles `bootstrap-session-exec.c` into a
private retained directory beside its receipt (or in TMPDIR). Compilation is
bounded to 30 seconds. It pins the binary with an open file descriptor and
SHA-256, checks the path's identity and pinned contents before and after
observations, and warms executable admission before starting the sample clock.
The first helper observation has a five-second deadline for cold executable
admission on macOS; the workload does not exist during this warmup. A stalled
helper still fails installation with exit 89. Subsequent workload observations
have a separate one-second deadline. The configured sampling interval (at most
100 ms) is the target cadence, not a guaranteed observation completion time.
The helper and source SHA-256 values are included in the receipt.

The canonical outer guard uses `--session-mode=new` and rejects any inbound
session pair. Nested timeout wrappers explicitly choose `--session-mode=inherit`,
which requires a live root, matching SID, helper SHA/source SHA, and a helper-
adjacent local admission receipt. The guard publishes its admission before
opening the workload gate. These local checks detect stale, malformed and
modified state; they do not authenticate against a caller deliberately forging
same-user files. Same-user emulation is outside this cooperative contract.

The child creates its session and waits on a pipe. Nested guards instead
create a process group in the inherited, authoritatively checked session.
Only a successful initial RSS and `getsid()` measurement releases exec.
The guard exports `SIMPLE_BOOTSTRAP_SESSION_ID` and an absolute
`SIMPLE_BOOTSTRAP_SESSION_EXEC` path to the workload. Both names are reserved
by the transcript writer, verifier, and final exporter; explicit environment
assignments cannot overwrite them. On Linux the persistent Perl supervisor
samples `ps` without shell pipelines. On macOS it compiles and pins the adjacent
`macos-process-observer.c` helper before workload creation, then keeps that
observer alive through private request/response pipes. `sysctl(KERN_PROC_ALL)`
provides one process metadata snapshot (PID, parent, group, zombie state and
microsecond birth identity). The supervisor applies the existing descendant,
retained-group and known-identity selection to that snapshot. Only selected
live members receive `libproc` RSS and `getsid()` queries, with birth identity
checked before and after each RSS read. Newly forked children are discovered
by the next snapshot; cleanup still freezes parents and takes another snapshot
before killing them. No host-wide RSS query or per-sample exec is used on macOS.

Guarded macOS portable-lock owner checks, including bootstrap EXIT cleanup,
also use the admitted observer path and SHA-256. They reject missing, symlinked,
privilege-bearing or hash-mismatched observers without falling back to setuid
`ps`. Two bounded `--identity` requests compare microsecond birth identity
around the kernel process-group query. The stored lock identity keeps the
existing C-locale `lstart` encoding, allowing guarded and standalone callers to
share locks. Each request has a five-second deadline and 256-byte output bound;
failed children are killed/reaped. Unguarded callers and Linux/MSYS retain their
existing identity backend, and stale-lock group recovery is unchanged. This
uses the progress watcher's trusted admission-directory model; checking a hash
before executing a path is not an atomic defense against same-user replacement.

The native protocol rejects incomplete/malformed/duplicate rows, caps each row
at 129 bytes including newline and the table at 131,072 rows, and validates PID
ranges. The kernel metadata allocation is independently bounded. A vanished
process is excluded only after ESRCH or a confirmed zombie; permission errors,
short reads, and changed birth identities fail the observation. Observer path,
binary/source SHA-256, backend, starts/restarts/errors and last PID are receipted.
The session helper remains verified during native observations. Observer failure
kills/reaps the observer; a fresh observer may be started for cleanup only,
never to resume the workload. A persistently broken observer kills the anchored
root group and reports unverified quiescence. SIGPIPE is ignored before helper
admission so early pipe closure produces a caught exit 89 with a receipt; the
workload receives its original SIGPIPE disposition.

A denied libproc/session detail query now receives one independent
`sysctl(KERN_PROC_PID)` check. It is omitted only when that successful query
proves the PID absent, or returns the exact expected PID/birth identity in
zombie state. A live process, reused PID, short metadata reply, or denied
metadata check still fails closed with exit 89. Denial diagnostics retain the
original operation/errno and record the proof outcome. This does not make a
live protected process measurable or authorize ignoring denied RSS.
Denial diagnostics also record bounded, whitespace-sanitized kernel command
name, parent/group/session IDs and effective/real UID. On detail EOF the
supervisor records its expected root/session, retained/current group anchor
identities, and the selected snapshot's ancestry (cycle checked, at most 32
rows). These are failure diagnostics, not a change to ownership selection or
permission handling. A failed `getsid` in the diagnostic is recorded as -1.

Sampling failure, malformed output, or a sample exceeding its one-second
observation budget causes exit 89. Scheduling uses the remaining
interval budget, rather than adding a full sleep after measurement. Scheduler
delays are reported as `sample_gap_max_ms`; this is not a real-time guarantee.
Receipts also report `observation_budget_ms`, `sample_duration_max_ms` for
completed observations (including cleanup), and `sample_overruns` for those
exceeding the target cadence. No extra cadence sleep follows a slow sample.

RSS breach returns 88; timeout returns 124; observed session escape returns
90; installation, helper integrity or measurement failure returns 89.
Ordinary child status propagates.
Timeouts retain TERM and the supplied grace period, then force cleanup. RSS
breaches freeze observed members/groups immediately, rediscover descendants,
and kill repeatedly until three samples show no live observed members.
Observed escaped groups remain tracked after their leader exits, capturing
children forked between measurement and termination. Startup and each retry
produce independent receipts; Stage 2 archives the first receipt with its
before-cache-retry log. Phase verification receipts remain under its TMPDIR.

## Scope and limits

**This is emergency monitoring and sampled evidence, not a kernel memory
limit or a strict whole-tree containment guarantee.** A process can fork,
change session, and become reparented entirely between samples. Such an
unobserved process cannot be recovered portably from later `ps` ancestry.
Independent review reproduced this with an immediately exiting parent and
an escaped child. Supported launch paths now preserve the inherited session
contract and the guard rejects observed SID changes. This is detection and
cooperative launch admission, not OS enforcement against every `setsid()`
syscall. It requires binaries built from the updated process-launch sources;
old prebuilt Simple binaries can still create new sessions and be rejected.

`quiescent=1` means the observed descendants and retained process groups are
empty. It does not establish absence of all possible escaped descendants.
Receipts explicitly include `containment_scope=observed-descendants-and-process-groups`
and `hard_memory_limit=0`. The direct child remains unreaped until signaling
ends, anchoring the root process group against PID reuse. Escaped group signals
require a fresh, matching leader identity; other observed descendants are
signaled individually after validation. On Darwin, cleanup takes fresh sysctl
metadata snapshots without RSS or session-detail queries, so a persistent
detail permission failure still permits validated STOP/KILL of retained groups
and their descendants, including after the root dies. The failed measurement
still returns 89; successful cleanup may record `quiescent=1`. If metadata
itself remains unavailable, cleanup kills only the anchored root group because
cached escaped identities cannot be validated; it returns 89 and records
`quiescent=0`. A configured threshold also permits growth between samples.
Strict host protection needs an independently admitted OS containment mechanism
(for example, a kernel-enforced aggregate limit), not this receipt alone.

## Verification

The unit fixtures cover below/above cap, observed escaped groups, concurrent
forking, orphan cleanup, startup refusal, sampling failure while running,
invalid limits, preserved stdin, timeout/grace, retry receipt preservation,
PID/PGID reuse, retention of the root identity sentinel, installation failure,
helper replacement, SID evidence, nested groups, and reserved-name attacks.
Existing phase command-owner and Stage 1 native authority tests passed on
macOS arm64. The latter now canonicalizes its temporary path to account for
macOS `/var` versus `/private/var` aliases.

A 3,500-function `cc -O2 -c` fixture measured 4.810 s median without the guard
and 4.817 s with the initial 100 ms sampler (three runs each, +0.13%). This
is a historical **pre-helper** baseline, not integrated performance evidence.
An interleaved run after helper integration measured 2.0245 s plain versus
2.4075 s guarded (three each, **+18.9%**, approximately 383 ms per invocation).
The receipt recorded peak 296,320 KiB and 40 authoritative SID observations.
This is a material regression on that short native workload and is recorded in
`doc/08_tracking/bugs/bootstrap_rss_guard_helper_startup_overhead_20260921.md`.
No Simple bootstrap performance gate is claimed.

The 2026-09-22 native observer check measured 8.836 s plain versus 10.281 s
guarded median across three interleaved 3,500-function compilations on this
loaded host (+16.36%, including both helper builds/admission). The final receipt
had 96 samples, maximum sample duration 18.98 ms, maximum start gap 113.41 ms,
zero sample overruns, zero observer restarts/errors, and peak 308,208 KiB. This
does not resolve the invocation startup overhead report or establish bootstrap
performance. The measurement covers the native syscall backend while protocol
failure handling was being tightened; it is not an immutable release benchmark.

An integration attempt subsequently encountered an unresolved native detail
EOF before compiler work. The observer now logs syscall/short-read operation,
PID, return size and errno, or expected/actual birth identity; the supervisor
includes the requested PID/identity on EOF. This diagnostic-only change keeps
the same fail-closed policy. Deterministic syscall/exit-transition tests pass,
but the observed bootstrap EOF has not been reproduced or behaviorally fixed.

## Delivery state

Focused native cap/escape/fork/orphan/stdin, PID identity, session admission and
tampering, timeout/grace, slow/hung observer and protocol checks are recorded in
`doc/08_tracking/bugs/macos_watchdog_hostwide_ps_timeout_20260922.md`. No bootstrap
retry was run after its three-cycle limit. Source-matched bootstrap verification
remains required before claiming the original build failure resolved end to end.
