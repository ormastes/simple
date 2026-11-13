# Windows Container stream detail design

The first source slice is `windows_managed_stream_owner_v2`: a portable wrapper
selects Windows-only launch, policy and byte-I/O modules. The existing PTY owner
retains all Job/process/pipe/event/attribute/file/CNG/allocation identities in its
nonreused generation-checked slots. Legacy integer PTY calls reject managed
slots. Raw stdout and stderr are deliberately merged; this is not a TTY or a
claim of separate output channels.

Admission validates exact CPU quantization and host prerequisites, pins and
hashes at most 256 MiB of the helper image, checks the launch clock during the
bounded hash loop, builds typed argv and a replacement environment, and creates
private pipes with an explicit inherited HANDLE_LIST. It configures and reads
back Job aggregate memory and hard CPU limits before suspended process creation.
After Job assignment, parent child-only pipe ends close before the final clock
check and resume. Failed admissions return their cleanup lease.

Writes accept one bounded prefix into retained OVERLAPPED storage; zero means
backpressure. Ambiguous completion disables further submission to prevent replay.
Reads expose bounded bytes to one logical reader. Collection requires observed
leader exit, exact Job emptiness, completed pending I/O and drained output or an
explicit cancellation. A cancellation request is not a terminal receipt. Failed
native releases retain their exact identities for cleanup; historical failures
are not rewritten into successful qualification.

The next provider slice uses these raw pipes solely for a pinned private Engine
broker. Its API1.48 wire codec bounds headers, control bodies and Docker mux
frames; internal templates and birth receipts remain SDN. Native Engine IDs are
observed values. Requested exec User and observed container Config.User are
separate from an unavailable Windows exec-token observation. Required native
pipe, private-root persistence and authenticated ongoing input/resize consumers
must be connected before advertising terminal support.

The V3 planning checkpoint embeds the shared `ContainerExecRequestV3`, including
the exact parent native runtime identity. Its public plan digest binds helper
identity and budget, installed provider identity, policy and private broker
template digest. The private template contains the canonical request bytes and
is bounded to 256 KiB of UTF-8. Literal environment values remain private.
`WindowsSimpleContainerAdapterV2.stream_plan_v3` checks retained authority and
freshly inspects the exact running container before returning the plan. A plan
does not launch the helper, create an exec, or grant input/resize authority.

Helper admission must preserve the existing reservation domains: the operation
payload hashes the original `HostReservationIntentV1`, whose `plan_digest`
hashes the canonical `HostHelperPlanV1`; that helper plan's `request_digest`
binds the stream plan digest. Exec admission is separate and uses the shared
host-verified exec carrier. An actual exec birth maps its observed native ID to
the exact parent, exec request, provider and stream template before start.
These planning and birth-binding cases are authored but NOT_RUN; the shared V3
open facade and private broker are still required consumers.

The parent provider baseline and exec-control identity occupy distinct fields.
`exec_control_identity_digest` is required for exec and absent for attach. The
generic exec birth's provider field identifies the exec-control observation;
it cannot be filled from the parent CLI provider baseline or a policy hash.
The signed host exec intent binds both identities, the request, and parent
operation/assignment/controller references. The admission carrier retains that
original intent; the native write deadline still binds the raw exec request
digest and child operation. The adapter's synchronous planning entry refuses
exec planning; its owned asynchronous control probe queries actual Engine info
and the exact retained container, validates the full process-isolation binding,
and collects both connections before exposing an observation. The separate
`stream_plan_with_control_v3` entry preserves the probe on every result and
consumes only that completed observation. The shared asynchronous facade and
verified Host broker delegation remain required integration steps.
