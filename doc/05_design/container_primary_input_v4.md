# Primary container input through smux V4

Status: consumed source implementation, **NOT_RUN**. This slice adds Linux
primary input. A subsequent Linux geometry source slice is described in
`container_primary_geometry_v1.md`; Caret, Windows and native qualification
remain pending.

## Authority and consumed route

The configured authenticated server installs
`runtime-primary-control-v4 BASE64URL_CANONICAL_SDN`. It uses the same protected
control policy, local owner principal, bounded issuer, attachment leases, and
Host root as V1. V1 request/reply schemas retain their unsupported input/resize
semantics. V4 carries the extra attempt information required for real input.

The service credential represents the installed trusted local owner described
in `doc/04_architecture/smux_runtime_control_owner_v1.md`, not an arbitrary
remote holder. Consequently nonce-free `revoke` is owner administration for the
selected kind and exact revision. Input effects additionally require the current
lease bearer. V1 rejects nonce fields on administrative revoke; an invalid input
bearer cannot retire a healthy holder. Geometry and Input remain distinct issuer
rights; an uncertain Input attempt does not revoke Geometry metadata authority.

The V4 envelope has exactly six fields: `version: 4`,
`kind: smux-primary-control-request`, canonical V1 `controlRequest` text,
`attemptSequence`, `offset`, and `maxBytes`. Input requires an explicit positive
attempt, byte offset inside the payload, and bounded prefix length. The later
Geometry extension accepts positive resize attempts with zero offset/maxBytes;
legacy resize zero is decoded but cannot execute. Other actions require zero
attempt metadata. SDN is limited to 2800 bytes, its token
to 3734, and the existing complete authenticated frame to 4096 bytes.

## Current target and effect ownership

Target resolution borrows the canonical adopted pane session. It checks the
actual primary binding, session identity, adoption fields, current service epoch
and child incarnation, client attachment, and executing parent/helper journal
rows. The common port correlates the exact provider runtime, host scope and
workload/binding digests with the retained primary plan. A fully released V3
tombstone may coexist with a V4 UID; retained opposite-domain state cannot be
treated as an absent binding.

The session keeps its native reference private. The new common install, revoke,
state, and write operations use that exact grouped native slot. No second
session, input transport owner, reader, process, or provider is created. The
lease metadata itself is not a grant: only the trusted in-process composition
calls the port immediately after the live issuer check. The common port repeats
lease, target, adoption, principal, bearer, revision, and clock correlation.
Native locking checks the full grouped identity, revision and monotonic deadline
at the actual single nonblocking write. No helper PID is used as workload
identity, and no app-side engine command or raw pane write is introduced.

Native revision/attempt values are bounded by `1152921504606846975`.
Milliseconds-to-nanoseconds conversion checks the smaller deadline ceiling
before multiplication. Generic pane input, terminal-generated replies, paste,
and geometry remain guarded; only the explicit input route consumes the right.

## Native synchronization and lifecycle

After issuance/revocation, periodic expiry checks, and generic dispatch changes
such as detach or attachment replacement, the server synchronizes canonical
pane gates before replying. It observes the live issuer and current target,
revokes any mismatched native holder, then installs only the exact eligible
lease. A fixed deadline is never extended by inspection or reconciliation.
Explicit primary helper cleanup first retires its issuer records. Actual
native-cleaned sessions may be skipped because their exact native gate was
closed; metadata retirement alone does not justify skipping a live session.

Failed install/revoke/state receipts remain `native-pending` in V4. Issued
metadata is distinguished from an installed usable gate. The server retains
`input_sync_error`, retries synchronization through actual native observation,
and refuses stop while uncertainty remains. V1 administrative replies report
synchronization pending instead of falsely claiming native completion.

Global discovery and binding replies do not promise active input. The V4 control
reply reports `inputSupported: true` only for a current checked lease and actual
matching native state with no pending synchronization or unknown prior attempt.
`geometrySupported` and `interactive` remain false. The discoverable protocol
name does not qualify native behavior or Windows support.

## Explicit attempts and receipts

Before a write, the same control owner reserves the complete canonical request
digest, immutable session identity, native target/nonce/revision/deadline tuple,
explicit attempt sequence, and requested byte bound. It initially records
`unknown` with `acceptedBytes: -1`. Every post-effect return retains the observed
disposition and prefix, including malformed or missing receipts and reply errors.

Exact retries return the cached observation without writing again. Changed
payload/range under the same attempt and older attempts are refused. Native
sequence admission independently permits only the next explicit attempt. A
recorded zero or partial prefix is reported as such; the client must explicitly
choose any later attempt and range. No code automatically increments an attempt,
retries bytes, rotates a lease, or interprets a lost reply as non-delivery.

Unknown outcomes block subsequent attempts and new Input lease issuance for the
same binding, including V1 issuance and native reinstallation. Rotation is not
proof that earlier bytes were not delivered. Read-only receipt refresh can turn
Unknown into Recorded only when the canonical native last tuple matches the
already reserved request and its prefix fits the saved bound. Native history
contains no payload digest and cannot reconstruct a missing request identity.
Inspect can report/reconcile retained receipts after revoke or expiry without
renewing input authority; unavailable history remains Unknown.

The receipt registry holds at most sixteen binding records. It never evicts an
Unknown record to admit another binding. A newer known attempt may replace a
known prior receipt; old queries are rejected/unavailable, never reported as
zero-byte non-delivery. Unresolved Unknown receipts also block server stop.
There is no automatic discard or force-ack path in this slice; an unavailable
native history can therefore require explicit future operator reconciliation.

## Verification and next work

Seven new codec scenarios and seven pure input-guard scenarios are authored.
Existing issuer and route specs gain one scenario each for shared-issuer Unknown
rotation/selected-kind independence/stop refusal and authenticated V4 routing
with administrative revoke shape. These sixteen scenarios are **NOT_RUN** under
the prior six-cycle runtime campaign cap. Pure lease/plan/native-receipt metadata
fixtures do not instantiate native sessions or prove delivery.

Successful configured route execution, native install/revoke/write locking,
actual partial/EAGAIN outcomes, callback/receipt loss, detach/expiry races,
post-cleanup receipt behavior, and native owner retention remain **NOT_COVERED**
by these source tests. Existing native primitive self-checks were not rerun.
No latency, throughput, or RSS qualification is claimed. The path performs
bounded in-memory issuer/journal checks, fixed-size native state queries, and
one write; it does not probe the provider or read policy files per byte. The
bounded synchronization sweep visits at most eight panes and sixteen leases.

The subsequent Linux geometry slice implements a typed container-resize
exchange, fresh exact-parent/TTY observation, and authorized bounded Unix-socket
provider operation in source; runtime qualification remains pending. Windows
still needs its real primary attach broker. Caret can consume this protocol only
after the complete lifecycle and these native effects are qualified.
