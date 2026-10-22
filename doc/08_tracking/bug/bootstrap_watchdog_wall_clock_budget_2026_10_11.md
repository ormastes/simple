# Bootstrap watchdog elapsed budgets follow wall-clock adjustments

GitHub: [#3136](https://github.com/ormastes/simple/issues/3136).

Status: OPEN (P1). Source repair and controlled-clock contracts; release and
cross-platform workload qualification remain pending.

## Defect and evidence

At release `e2d56c23365c8f2fe4a59e13bb2b7c0de1c0cd3b`, the watchdog uses
`Time::HiRes::time` for 25 duration/deadline reads. A forward wall-clock step
can expire a compiler/helper/observation/grace budget early; a backward step
can extend it or produce a negative sample duration. These are elapsed-time
contracts, not civil timestamps.

The retained 83d8/b62 attempt1 ended with watchdog timeout124/quiescent1 and
896 staged objects. Its reported native elapsed duration was 3246.171578s
against the requested 3543s watchdog budget. This motivated investigation;
**an actual host clock step and causation of that timeout are unproven**.
Do not relabel the historical failure or infer compiler completion.

## Repair

Use `clock_gettime(CLOCK_MONOTONIC)` through one accessor for all existing
elapsed starts, deadlines, grace checks, sample durations and cadence. No
process ownership, signal, RSS policy, source/cache fingerprint or receipt
semantics change. Keep the canonical scripts/resource plus scripts/bootstrap
helper layout; copying only the Perl file is not a deployable watchdog.
There is no wall-clock fallback when a host lacks the required clock.

## Reproducer and prevention

Run `python3 scripts/check/check-watchdog-monotonic-budget.py` on a host with
Python3, Perl and Test::More. It extracts the actual canonical accessor and
four budget expressions without executing watchdog main or a workload. Eight
assertions control monotonic and civil clocks independently: forward/backward
wall jumps around timeout, sample duration and grace, sampling cadence and
the accessor clock selector. The old implementation cannot satisfy the source
extraction/clock contract. No host clock changes or long sleeps are needed.

The same generated eight-assertion Perl program passed once for diagnostic
watchdog SHA256 `6fb208db7ebc4ddd867041c1b3ec6e28688e8d52338c29a7fadfe50594c07eac`.
Canonical executable bytes differ only in a comment. Exact generated-program
identity binds that evidence; no green tests were rerun. Retained result SHA256:
`ef968c77c89f030f512dda0f942cece6837eedd4577fefa48ebd9fbce7bf35af`.
At that originating lane, the new portable wrapper was source-reviewed but
not executed. Later isolated port executions are recorded below.

## Initial isolated port qualification

The historical eight-contract PASS and retained result hash above are the
originating lane's observations. Their generated-program/result receipt was
not accessible in this review, so that claim was not reused as a local PASS.
The unchanged new portable wrapper ran once against this port's exact
canonical watchdog: eight assertions PASS, child/wrapper exit0, empty stderr.
The extracted generated program and TAP are retained in
`reviews/watchdog-monotonic-port-dbd/`, with exact wrapper/source/program pins
in actual-controls-receipt.json. Only extracted clock expressions ran; no
watchdog main, compiler, workload or actual host clock adjustment executed.
Linux installed Time::HiRes CLOCK_MONOTONIC availability and canonical Perl
syntax passed once. Other hosts and full workload integration remain UNRUN;
historical timeout clock causation remains unproven.

## Checked startup correction

Independent review confirmed the installed Time::HiRes provider can return
-1 with errno22 and no exception for an unsupported clock ID. Merely importing
clock_gettime does not establish runtime clock availability. A checked startup
helper now requires a defined nonnegative monotonic value for the first
`$started` assignment, before any helper installation or workload fork. Failure
refuses startup with no civil-clock fallback; a legitimate zero is accepted.

The runtime accessor and existing process/RSS/cleanup paths remain unchanged.
This validation is deliberately startup-only: throwing on every later clock
read could bypass existing workload cleanup. Steady-state provider-fault and
lifecycle behavior remain inherited and unqualified; no broad fault-handling
claim is made.

The changed-input portable wrapper executed once:12assertions PASS, exit0,
empty stderr. It extracts both actual helpers and verifies the checked startup
caller precedes every fork site. Added controls reject -1 and undef, propagate
a startup provider exception and accept zero. Exact program/source/wrapper
pins and TAP are retained in changed-startup-controls-receipt.json; the initial
eight-assertion receipt remains preserved as historical. No watchdog main,
compiler/native workload or host-clock adjustment ran. Historical timeout
clock-step causation and cross-platform workload qualification remain unproven.

## Platform limits

- Linux/WSL: existing diagnostic controlled-clock contracts PASS; this does
  not constitute full compiler or application qualification.
- Native Windows: upstream Perl5.40 Time::HiRes implements CLOCK_MONOTONIC
  with QueryPerformanceCounter. Installed Perl/version support and full
  watchdog/session behavior are UNEXECUTED here.
- macOS: upstream Time::HiRes provides native clock_gettime or a Darwin
  mach_absolute_time clock implementation. Installed support and workload
  behavior are UNEXECUTED here.
- FreeBSD/OpenBSD: platform CLOCK_MONOTONIC exists; the installed Perl must
  expose it. Host integration and watchdog behavior are UNEXECUTED here.
- SimpleOS: this is a hosted Perl supervisor. No native SimpleOS Perl or
  monotonic-provider qualification is established; do not claim support.

Clock availability depends on the Perl build; unavailable support must fail
before workload creation, never substitute civil time. Suspend accounting is
platform-specific; this repair promises resistance to civil-clock steps,
not a new cross-platform suspend-time policy.

References: [Time::HiRes contract](https://perldoc.perl.org/Time::HiRes),
[Perl5.40 native providers](https://github.com/Perl/perl5/blob/v5.40.0/dist/Time-HiRes/HiRes.xs),
[FreeBSD clock contract](https://man.freebsd.org/cgi/man.cgi?query=clock_gettime&sektion=2),
[OpenBSD clock contract](https://man.openbsd.org/clock_gettime.2).
