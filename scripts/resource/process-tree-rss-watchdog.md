# Sampled bootstrap RSS guard

`perl scripts/resource/process-tree-rss-watchdog.pl --max-rss-kib=5859375
--interval-ms=100 --timeout-seconds=660 --receipt=/absolute/run.rss.env
-- COMMAND ARGS...` supervises one command on macOS/Linux. The production
default is decimal 6 GB (5,859,375 KiB). Overrides may lower it; the absolute
configuration ceiling is 6 GiB (6,291,456 KiB). The ordinary compilation
acceptance target remains **less than 1 GiB**, assessed separately.

The child creates its session and waits on a pipe. Only a successful initial
RSS measurement releases exec. One persistent Perl supervisor samples `ps`
without shell pipelines. Sampling failure, malformed output, or a sample
exceeding its interval budget causes exit 89. Scheduling uses the remaining
interval budget, rather than adding a full sleep after measurement. Scheduler
delays are reported as `sample_gap_max_ms`; this is not a real-time guarantee.

RSS breach returns 88; timeout returns 124; ordinary child status propagates.
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
an escaped child. Native process helpers can create new groups/sessions;
the repository does not enforce a prohibition on that behavior.

`quiescent=1` means the observed descendants and retained process groups are
empty. It does not establish absence of all possible escaped descendants.
Receipts explicitly include `containment_scope=observed-descendants-and-process-groups`
and `hard_memory_limit=0`. If sampling remains broken, cleanup kills known
groups but cannot validate cached escaped PIDs; it returns 89 and records
`quiescent=0`. A configured threshold also permits growth between samples.
Strict host protection needs an independently admitted OS containment mechanism
(for example, a kernel-enforced aggregate limit), not this receipt alone.

## Verification

The unit fixtures cover below/above cap, observed escaped groups, concurrent
forking, orphan cleanup, startup refusal, sampling failure while running,
invalid limits, preserved stdin, timeout/grace, and retry receipt preservation.
Existing phase command-owner and Stage 1 native authority tests passed on
macOS arm64. The latter now canonicalizes its temporary path to account for
macOS `/var` versus `/private/var` aliases.

A 3,500-function `cc -O2 -c` fixture measured 4.810 s median without the guard
and 4.817 s with the initial 100 ms sampler (three runs each, +0.13%). This
only suggests modest overhead for that native compilation workload; it is
not a Simple bootstrap performance result. The cadence correction reduces
sleep by sampling time, and additional real bootstrap measurements remain
necessary before claiming a Simple compilation performance gate.
