# Windows Docker process-only request admission

Status: NOT_RUN. Authored manual mirror of
`test/03_system/app/orchestrator/feature/windows_docker_process_contract_spec.spl`.
Admitted SPipe/docgen/sspec-maintain execution remains outstanding; this is not a
generated pass report. Fixtures are synthetic and never start Docker.

Requirements: REQ-WDP-001, REQ-WDP-002, REQ-WDP-003, REQ-WDP-005, REQ-WDP-006.

| Scenario | Reader action | Expected assertion |
|---|---|---|
| Explicit compatibility tuple | Supply selected host kernel and image OS-version strings. | Values are individually retained; their differing formats are accepted without a compatibility claim. |
| Engine route | Replace local named pipe with a remote daemon or resolve Docker through PATH. | Policy refuses the endpoint or executable. |
| Identity and bounds | Omit engine identity, use generation zero, infinite timeout or excess output. | Policy refuses execution. |
| Immutable image | Supply tag-only or shortened digest. | Request refuses mutable/partial identity. |
| Resource policy | Ask for NAT, zero CPUs or undersized memory. | Request refuses unsupported network/limits. |
| Entrypoint bounds | Omit the command or supply NUL. | Request refuses unsafe data before execution. |
| Typed arguments | Use a spaced executable, spaces, shell-looking text and an empty argument. | Exact argv elements remain separate; process isolation and ContainerUser are explicit. |
| Request binding | Change argument boundaries, CPU allocation or engine identity. | Canonical semantic digest changes. |
| Native identity | Supply a full lowercase ID, prefix, name or flag. | Only the full native ID is admitted. |

The tests compare concrete errors, fields, digest differences and argument indices.
They do not prove Windows API quoting, resource enforcement, engine availability,
image compatibility, actual process isolation, or ordinary-client authorization.

The SDN scenarios additionally round-trip quoted/newline/empty arguments, reject
duplicate/unknown/missing/typed fields, reject modified digests and schema versions,
require canonical serialization, and refuse a record bound to another engine policy.
Policy is trusted local input and never decoded from request payload bytes.

An explicit working directory is an additive version-two request. Version one
keeps the image default and its previous canonical shape. Version two binds the
selected absolute path in the semantic digest and actual `--workdir` argv; relative
paths are refused. Action projection refuses the unresolved version-one default.

Additional negatives reject a directory in a version-one record, a version-two
record without its directory, and directory tampering without a matching digest.
An explicit drive root is a valid absolute working directory.


## Protected Windows workspace mount extension — NOT_RUN

Typed WindowsDockerMountV1 has host_root, guest_root and read_only; requests
default to an empty mounts array. At most one explicit bind mount is supported.
Mounted requests use canonical request SDN version 3 with required
workingDirectory and mounts: [{hostRoot, guestRoot, readOnly}]. Empty mounts
preserve the existing version 1/2 request serialization and digest branches.
Duplicate/unknown/missing/mistyped nested fields, array limits, noncanonical
records and digest tampering are rejected. The v3 digest binds each typed mount
field, explicit work directory and administrator workspace root.

Policy workspace_root defaults empty. Nonempty roots select canonical policy
SDN version 2 with workspaceRoot; legacy empty-root policy v1 serialization is
preserved. Roots must be strict absolute Windows drive paths deeper than a bare
drive, without trailing separators. A mounted host_root must be a strict
descendant of the configured protected root, never the configured root itself.
Working directory must equal guest_root or be a backslash-delimited descendant.
Root comparisons are exact and conservative; source does not guess Windows
case/normalization aliases. Path validation rejects mount CSV comma/equal option
injection, quotes, control characters, pipe delimiters, traversal, dot components,
trailing dot/space aliases, alternate streams, wildcards and relative/UNC forms.

The actual Docker create argv includes a single --mount value
type=bind,source=<host_root>,target=<guest_root> with an optional readonly flag,
and the explicit --workdir. No bind-create-src option is emitted: Docker must
reject a missing source rather than silently creating an unrelated directory.
The administrator provisions a protected parent; lexical admission alone does
not establish ACL/SID protection or eliminate hostile directory replacement.
Native path identity/no-follow checks belong to the execution adapter.

Authored positive vectors cover typed round-trip, actual argv, read-only and
read-write digest changes and protected-root binding. Negative vectors cover
root/outside/sibling-prefix attempts, absent workdir, out-of-mount workdir, more
than one mount, unsafe paths and strict nested records. Existing request v1/v2
scenarios remain in the executable specification; unknown schema checks now use
version 4 because request version 3 is defined.

No compiler, test, Docker create or native Windows execution was run for this
extension. Windows bind mounts require a local source directory and an allowed
empty/nonexistent destination (or a different drive); syntax/source vectors do
not establish that a particular image/host path pair works.

[Docker bind mounts](https://docs.docker.com/engine/storage/bind-mounts/) documents
CSV mount options, readonly semantics, missing-source behavior and the actual
Mounts fields used for inspection. [Docker Windows mount constraints](https://docs.docker.com/reference/cli/docker/container/run/)
documents Windows source/destination restrictions. These references are not
native execution evidence.


Explicit primary terminal/stdin extension: request SDN version4 binds the
default-false terminal_tty/stdin_open fields when either is requested. CLI
create emits the corresponding actual flags, and exact native inspection checks
Tty/OpenStdin/StdinOnce/AttachStdin under official CLI semantics. Existing false
request branches keep their previous bytes/commands. Focused executable source
and NOT_RUN manual: windows_docker_primary_terminal_v4_spec.spl / .md in the
same system-spec directories. No native terminal qualification is claimed.
