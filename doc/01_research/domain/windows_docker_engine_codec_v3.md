# Windows Docker Engine codec v3 primary-source findings

2026-11-07. Source research; **NOT_RUN** for all Windows and Engine effects.

[Docker Engine API1.48](https://docs.docker.com/reference/api/engine/version/v1.48/)
defines explicit versioned paths for info, exact container inspection, attach,
exec-create/start/inspect and container/exec resize. The codec initially admits
only administrator-selected1.48; there is no negotiation or fallback. JSON is
used only for this required external protocol; internal records remain SDN.
Attach documents101 upgrade and200 non-upgrade streaming. Exec-create returns
201; ordinary inspection/resize returns200. Exec-start documents200 interactive
streaming. The API documents multiplexed stdout/stderr with an eight-byte header
when TTY is false and raw data when TTY is true. Codec preserves binary bytes,
checks reserved bytes/tags/lengths, and never equates EOF with workload absence.

[Docker API hijack history](https://github.com/moby/moby/blob/master/api/docs/CHANGELOG.md)
records Upgrade hints for both attach and exec-start.
[Official hijack description](https://github.com/moby/moby/blob/master/api/docs/v1.24.md)
explains the200 to101 transition when Upgrade is detected. These are the reasons
for endpoint-specific streaming acceptance; ordinary JSON endpoints never
accept an upgraded stream as a control response.

[Official Moby exec inspection](https://github.com/moby/moby/blob/master/daemon/inspect.go)
constructs actual exec ProcessConfig metadata. Its Windows branch can omit
false privileged metadata, and comments that the exec user value is unused on
Windows. Therefore absent/empty user and absent privilege are unobservable
optional facts, never invented observations. A nonempty conflicting user or true
privilege fails. Exact target container Config.User must be ContainerUser, and
immutable exec-create explicitly requests ContainerUser with Privileged=false.
This is request/configuration binding plus actual exec identity/argv/TTY, not a
claim about a Windows access token. WorkingDir/Env are not exposed by exec
inspection; their assurance is the immutable admitted request and persisted
birth mapping. Real token evidence needs a separately qualified native path.

[Docker CLI entrypoint semantics](https://github.com/docker/cli/blob/master/docs/reference/run.md)
explicitly state that --entrypoint clears the image CMD. That corrects an early
inference based only on emitted CLI argv. No empty-CMD inheritance bug is
claimed; actual command comparison is retained as a validation condition.


Codec review corrections (source-only NOT_RUN): exec DTO includes explicit
stdin_requested, used for AttachStdin and exact inspected OpenStdin comparison.
Docker multiplexed tag0 is the documented stdin echo routed to stdout; native_tag
is retained as0/1/2, with -1 for unframed TTY bytes. Partial payload length, rather
than tag0, distinguishes an active echo frame from idle state.

[Official API1.48-era Moby backend type](https://github.com/moby/moby/blob/v28.0.0/api/types/backend/backend.go)
defines ExecInspect.ExitCode as *int, and
[daemon inspection](https://github.com/moby/moby/blob/v28.0.0/daemon/inspect.go)
returns that pointer. JSON null therefore remains an absent optional exit_code.
A running snapshot also exposes no terminal exit; observed integer exit is
retained only for a nonrunning snapshot. The broker must additionally know that
this exec actually started before treating it as termination evidence; a
pre-start nonrunning object or stream EOF is not a completed workload receipt.
