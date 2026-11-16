# Windows cooperative Host execution V4

Status: SOURCE IMPLEMENTATION; AWAITING_VERIFICATION. No native, bootstrap,
compiler, runtime, SPipe or docgen campaign was started. Prior campaign limits
remain closed. This is a prerequisite for the persistent generic smux V5
consumer, not full Windows/Caret acceptance.

The canonical owner is the existing `HostServiceDomainV3`. The application calls
`host_service_execution_begin_v4(domain, request)` and then
`host_service_execution_step_v4(domain, continuation, cancel)` on the same
thread. Every turn returns that domain. A continuation contains stage state and
native command cleanup, never another Host root, capacity ledger or journal.
Pending turns have no response; an error with a retained continuation still
requires polling or cancellation. Host mutations and new attach authority must
be blocked while execution is pending. Existing terminal readers can progress.

Admission reuses the existing signed execution decoder, signature/snapshot
verifier, reservation oracle and capacity begin transition. Original packet,
request and plan are archived before the same journal commits execution. The
cooperative sequence is provider prepare, create, durable exact creation intent,
start, independent inspect and immutable observation. Capacity preparation does
not substitute for Docker image/engine preparation. The finite Windows Host
path now establishes this prerequisite too; Linux flow is unchanged.

Immutable carrier origin (native versus explicit fixture), policy and scope
are compared before registry access; Host continuations additionally bind the
actual journal root/lease/authority metadata. On Windows every registry access
requires the canonical thread, including scripted fixtures. Non-Windows explicit
fixtures alone bypass the unavailable Windows guard. Mode or owner substitution
retains the continuation and performs no command or registry mutation.

Provider progress uses a canonical nonreused registry so copied progress values
cannot replay a command stage; completed entries release captured bytes when
the common owner consumes them. Finite and cooperative Docker operations share one command reducer and the same
inspection decoder. Engine, image, exact container ID, request labels, managed
scope, isolation, configured user, network, resources, mounts and TTY are still
validated. The cooperative path does not call the finite Docker capture owner.
It checks native machine/boot-counter continuity and sequences actual engine
checks as commands. No helper PID is used as container identity.

The new Windows command owner uses the existing canonical Windows thread guard,
explicit executable/cwd/environment, suspended CreateProcess, a kill-on-close
Job and an explicit inherited-handle whitelist. Begin validates and retains a
slot; steps prepare, create pipes/Job, create suspended, assign, resume, drain,
observe and clean. Every wait is zero-time. Each output step reads at most 4096
bytes per stream after PeekNamedPipe; cleanup retries one handle/allocation at a
time. Actual Unix expiry is sampled immediately before CreateProcess and resume.
Process timeout uses monotonic elapsed time with an explicit resumed flag, so a
zero uptime is valid. Errors retain exact native resources until released.
There are no new runtime-C exports in this command owner.

Each Host turn refreshes current policy/context. Expiry/revocation/cancellation
prevents later launch and cancels only the retained command helper. It does not
kill a workload or release capacity. Journal/current-owner drift still permits
cleanup through that exact retained helper lease, with no new command or archive
publication through the rejected journal. Unknown outcomes remain charged and
require existing reconciliation; process-memory continuations are not restart
recovery or power-loss durability.

Read-only `simple_container_inspection_begin_v4(owner, request)` needs no launch
or attach grant. Its command timeout comes from installed policy. Successful
actual native inspection can mint a private adapter marker for the primary
planning/begin consumer. It binds canonical request bytes, full runtime identity,
provider pin, running phase and a conservative monotonic bound sampled before
actual inspect command admission. Cleanup/publication never renews that bound. Nonreused canonical
slots invalidate copied aliases on consumption; the existing native thread
barrier protects consumption. The marker expires after the smaller of installed
timeout and one second, and is consumed before binding/current-host checks.
Planning and begin each need a new inspection. The marker is not a signed grant,
wire decoder or caller-supplied boolean; lower independent signed attach
verification remains required. Scripted inspection never mints it.

Qualification limits: four origin/domain cases cover both provider mode
substitutions, changed policy/scope and another actual journal owner. The
native-origin case requires Windows but stops before any command poll/child;
live native-child substitution remains unqualified. Three inspection-age cases exercise the production age
predicate with a real monotonic-domain sample and modeled delayed completion;
no native cleanup delay is executed. The nine command contract cases exercise pure production
validation/codec/timeout helpers, not Win32 calls. Six Host scenarios use real
signatures and a real Linux-backed shared journal with explicitly scripted
Windows command results. They check prepare-before-create, intent-before-start,
finite compatibility, cancellation/expiry charging, provider-alias replay and retired continuation
refusal. Native launch/assignment/resume faults, partial pipe output, failed
termination/release retries, actual monotonic/Unix clock races, marker use,
protected Windows journal integration, configured server V5 polling and restart
recovery remain NOT_COVERED by these fixtures and NOT_RUN. Final UTF-8 decoding
can process up to 16 MiB; fixed native calls, protected-policy refresh and whole
server latency/RSS are unqualified. A bounded amount of work is not a measured
latency guarantee. Legacy Windows process owner defects are recorded separately
in `doc/08_tracking/bug/windows_process_admission_cleanup_blocking_20261114.md`.
