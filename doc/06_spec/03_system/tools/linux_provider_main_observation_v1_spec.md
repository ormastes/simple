# Actual original provider main-process observation

Status: **AUTHORED_NOT_RUN**. No native build, test, service operation or engine
campaign ran for this source slice.

Executable: `test/03_system/tools/linux_provider_main_observation_v1_spec.spl`.

The disposable fixture must satisfy the actual supervisor/profile installation
contract. The test is the genuine supervisor service MainPID under the dedicated
UID. Its provider stays running, creates its own installed Unix endpoint, has
`Restart=no`, no `ExecStop`/`ExecStopPost`, `DynamicUser=false`, `RemoveIPC=false`
and no `RuntimeDirectory`. These fixture values exercise typed property reads;
they do not authorize a systemd stop transaction. Actual Linux pidfd/libc and
libsystemd support are mandatory. There is no synthetic owner, caller path,
unsupported skip, self-installation or process/service mutation by the cutoff.

1. Acquire the actual installed supervisor. This initial accepted factory may
   mask/reload/stop its installed **legacy activation units**; the fixture is
   disposable and must be provisioned by an administrator.
2. Continue through `begin_provider_cutoff_v1()` on that same owner. It retires
   active aliases before native acquisition and pins the actual original pidfd,
   proc identity, current manager and installed Unix peer. A failed observation
   does not become a successful cutoff.
3. Confirm actual original PID/incarnation/profile/manager agreement, a pinned
   socket identity, and a live original process. Observe the actual typed stop
   properties while receiving the precise refusal
   `provider-stop-transaction-ownership-unavailable`.
4. Confirm both prior active APIs reject the old alias. Close only the owned
   observation resources; the original global inhibition remains retained and
   no active alias is revived.

The preflight values are captured at initial acquisition. Later `current_v1()`
refreshes process/profile/manager/exit observations and returns those retained
preflight values. Its monotonic timestamp does not date fresh preflight sampling.

This API has no Ready variant, signal, provider mask, provider StopUnit,
restart, helper-closure, request-drain, inventory-release or genesis grant. A
natural original-process exit can be observed by the source, but this scenario
does not induce or qualify that path. Nonchild pidfd exit is not a reap.

**NOT_COVERED:** actual exit/reuse races, namespace substitution, peer handoff,
forked/copy cleanup faults, libc/link admission, deadline faults, native close
errors, interrupted submissions, complete stop-transaction ownership, escaped
helpers, unknown workloads, post-cutoff store observation and same-writer
handoff. No source-only case is presented as native evidence.
