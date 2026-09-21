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
assignments cannot overwrite them. One persistent Perl supervisor samples `ps`
without shell pipelines. Sampling failure, malformed output, or a sample
exceeding its interval budget causes exit 89. Scheduling uses the remaining
interval budget, rather than adding a full sleep after measurement. Scheduler
delays are reported as `sample_gap_max_ms`; this is not a real-time guarantee.

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
signaled individually after validation. If sampling remains broken, cleanup
kills only the anchored root group because cached escaped identities cannot
be validated; it returns 89 and records
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

## Delivery state

Committed at the user's explicit stop-and-push-as-is boundary. Helper integration,
core RSS, identity, deadline/grace, retry, reserved-env attacks, and phase authority
checks passed before the final explicit new/inherit admission changes. The final
mode/admission changes and associated revised fixtures have **not** received a
complete suite rerun or independent launch approval. Source-matched Simple
rebuilds and verification on the accepted PR head remain required. This is a
relaxed, unverified delivery state; the strict launch gate remains closed.
