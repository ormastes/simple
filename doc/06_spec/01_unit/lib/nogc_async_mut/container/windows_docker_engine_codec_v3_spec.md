# Windows Docker Engine API1.48 codec v3

Status: **SOURCE-ONLY NOT_RUN**. No compiler, specification, native pipe, Windows
process, Docker request or interactive session was executed.

Source: `src/lib/nogc_async_mut/container/providers/windows/docker_engine_codec_v3.spl`.
Spec: `test/01_unit/lib/nogc_async_mut/container/windows_docker_engine_codec_v3_spec.spl`.
Research: `doc/01_research/local/windows_docker_engine_codec_v3.md` and
`doc/01_research/domain/windows_docker_engine_codec_v3.md`.

Pure request DTOs cover info/container-inspect, attach with explicit stdin mode,
exec-create/start/inspect and exec/container resize. Only exact lowercase64-byte
hex IDs and explicit version1.48 are admitted. Exec argv, environment names and
values, canonical absolute Windows program/cwd, row/column ranges and serialized
size are checked. JSON is explicit Docker interoperability; no shell parsing or
HTTP negotiation occurs. Builders authorize nothing and perform no effect.

Fixed caps: header16KiB, control body256KiB, request body64KiB, output frame and
input feed1MiB; JSON depth32 and token preflight8192; at most1024 chunks/frames
per parse/feed and64 HTTP fields. Shared strict JSON rejects decoded duplicate
keys at every nesting level; lone UTF16 surrogate escapes fail rather than being
replaced. Required field/type/identity mismatches fail. Unknown bounded API
metadata remains compatible with Docker's open response schema.

HTTP parsing rejects malformed/duplicate fields, ambiguous CL/TE, unexpected
status/media/upgrade and oversized/incomplete framing. Content-Length and a
restricted chunked profile are supported. Chunk extensions and nonempty trailers
are refused. Chunk payload remains binary before strict JSON decoding. Terminal
response body and leftover bytes are separate; hijack preserves every initial
stream byte. NeedMore at actual EOF is a caller failure, never default200. The
native owner must bound aggregate receives/parsing under its deadline; repeated
small-buffer parsing and performance/RSS are unqualified.

Full container binding independently compares installed Windows engineID/kernel,
effective policy/scope fence, pinned image/ref, process isolation, ContainerUser,
network, CPU/memory, all ownership labels, exact cwd/Entrypoint/Cmd, and complete
zero/one bind mounts with Source/Destination/RW. Base container TTY and stdin
mode bind the typed v4 retained CREATE request. A caller cannot override the
expected TTY, and actual OpenStdin/StdinOnce/AttachStdin must match stdin_open
under official CLI semantics. Exec TTY is independent and checked against its
retained exec request. The codec depends on the v4 request contract.

Exec inspection checks exact container/exec IDs, argv, stream attachment, TTY and
exit fields. Missing/empty exec user and missing privilege remain optional
unobservable metadata. They are not access-token observations. ContainerUser and
unprivileged exec JSON are immutable request facts, with actual target config
binding; exec Env/cwd require the admitted request and persisted birth mapping.

Non-TTY output uses strict eight-byte headers, stdout/stderr tags and bounded
partial-header/payload state. TTY output is unchanged raw bytes. Input to Docker
is unframed and requires separate live authority. EOF does not prove exit or
absence. A private named-pipe/Job broker, admitted writes, actual birth
persistence, ambiguous-result handling, live resize and workload qualification
remain separate unfinished integration work. No host ConPTY is involved.


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
