# Retained Controller dispatch V3

Status: **SOURCE_AUTHORED_NOT_RUN**. Routing source cycle 5/6, canonical-custody
correction batch 2. Immutable R1/R2 remain at
`/tmp/controller-dispatch-owner-v3-20261115-r1` and
`/tmp/controller-dispatch-owner-v3-20261115-r2`; integrated69 is unchanged.
Initial cycle4 freeze is preserved at `/tmp/controller-dispatch-owner-v3-20261115-r3-initial`.
This single cycle5 batch corrects native guard Result-unit adaptation, actual
unregistered close disposition, and real fixture carrier/bounded-poll handling.
No runtime, compiler,
build, seed, native, socket, installed credential, OS ancestry or cleanup test
was run. The five payload files are new. Existing V2, Controller root/config,
IO, server and all earlier frozen candidates were not edited.

This is a **local Windows** route. Its protected setup and Host deployment
filesystem access do not implement cross-host transport. The Controller keeps
its own actual journal writer; the client never opens a Host writer.

The implementation is `controller_dispatch_owner_v3.spl`; the executable
source spec is `test/01_unit/lib/nogc_sync_mut/orchestration/controller_dispatch_owner_v3_spec.spl`.

## API and ownership

Registered `ControllerDispatchOwnerV3` is an opaque identity/revision handle.
Private canonical state retains the actual ControllerLocalRootV3, protected
HostServiceReadyReaderV1 and exact current HostServiceAuthExchangeV6. Handles
never contain capability snapshots. There is no independently opened journal,
second writer, restoration decoder or raw reply authority factory.

The sole private registry belongs to this leaf's capability custody, not a
parallel journal or authorization framework. At most 16 registered slots are live; only
fully retired slots can be reused. Checked monotonically increasing identities
are never reused, including when a slot is reused. The actual native Windows
origin/thread guard runs before **any** registry access, including busy,
capacity and identity checks. Origin failure touches no registry.

Every accepted step/close checks and consumes its current revision and marks
the slot busy before any lower effects. The complete latest returned custody
is published before exposing results/errors. Stale handles perform no phase or
native effect, do not poison canonical outcome, and return explicit error plus
the latest handle for deliberate adoption/cleanup. Busy refuses. At revision
ceiling, canonical state becomes cleanup-only; close can drain that state
without another increment, wrap, reset or phase restart.

`ControllerDispatchOwnedTurnV3` has `owner`, `completed`, `cleanup_pending`,
`outcome`, `response`, `error`, default `root_cleanup` and default DATA `phase`.
The caller replaces the sole canonical owner
on every return. `completed` means no local owner carrier remains; it never
means the remote execution completed or local consumed-close uncertainty was
success. First error remains nonempty after all carriers are consumed.
`cleanup_pending` describes local cleanup only. A working exchange is represented
by a present owner with completed=false, independently of cleanup_pending.
The default root_cleanup field stays nil for compatibility. A pre-registration
origin/capacity/identity/indeterminate refusal retains the actual input root in a
private cleanup-only unregistered owner arm, never as bare root cleanup. Its
step/close first native-guards, then compares against every active canonical
root using the existing native-token-only same_journal_owner_v3 port. A match
returns explicit duplicate refusal and the current registered handle without
closing or poisoning it. An indeterminate comparison retains the refusal arm;
only definite no-match permits actual Root.close. Its actual late close error or
unconfirmed disposition is recorded after the primary registration refusal. A
nil returned Root is never retried and actual closed=false remains completed=false,
with no invented carrier or claim of confirmed cleanup. Such an arm can never register,
launch, open setup or exchange. No registry is touched on origin failure.

Normal begin also dedupes actual native journal identity before registration,
including copied roots whose WAL/current metadata has advanced. Busy state
remains registered for identity-only comparison while phase access is blocked.
There is no separate origin Root copy/store stamp or duplicate writer registry.
The Root comparator is DATA identity, not liveness, WAL or launch authority.
`Owner.same_handle_v3(other)` is guarded read-only identity/revision DATA equality;
it never reads the registry or proves current revision, liveness or admission.

Production entrypoints:

| Function | Purpose |
| --- | --- |
| `controller_dispatch_begin_v3(root,uid,packet,resume=false)` | Signed generic dispatch through existing actual assignment/reservation state machines. |
| `controller_dispatch_control_begin_v3(root,uid,action)` | Explicit remote inspect/progress/cancel only, using original retained execution. |
| `controller_dispatch_inspect_begin_v3(root,uid)` | Inspect wrapper over the control route. |
| `controller_dispatch_service_begin_v3(root,action)` | Actual status/service-stop only; no synthetic UID, packet or grant. |
| `controller_dispatch_step_v3(owner,cancel=false)` | Progress the exact retained exchange; cancel is LOCAL transport cleanup only. |
| `controller_dispatch_close_v3(owner)` | Close exchange/socket, protected reader, then same actual Controller root. |

`response` is exact typed HostControllerStatusV3 payload for successful service
status; canonical HostServiceOperationReplyV6 for service-stop/error and
authenticated pending; existing ControllerExecutionReplyV2 for terminal dispatch
observation. Every authenticated outer reply and nonempty inner payload is
archived through the actual Controller journal. Unknown/error preserves the
last cached pending response. `outcome=remote-pending` is data, never execution
success. `outcome=unknown` survives later successful local cleanup.

## Actual effect chain and replay gate

The retained root supplies pinned installed configuration/policy and its actual
workload journal. Reader open uses installed setup path, setup pin, Host
deployment locator and expected journal authority DATA digest. That expected
digest reuses the existing private formula from host_capacity_owner_v1:37–40:
SHA256(`HOST-CAPACITY-AUTHORITY-V1\n` + physicalHostId + `\n` + `host-` +
enrollmentDigest + `\n`). This shared formula dependency does not grant any
authority. The actual reader proves protected selector/ready publication
binding; it does **not** replay or verify the Host WAL.

Each active phase yields the exact current exchange, whose actual one-use
verified proof must be taken before any next-phase action. Its socket is closed
and registry exchange consumed before beginning the next exchange in the same
uninterrupted call. Any consume, archive, oracle, retention, clock or admission
failure enters cleanup. No externally yielded bool/phase permits another send.
Public handle copies cannot act on an older capability snapshot: all actual
custody is canonical. This does not turn raw DTOs into native admission or
provide cross-thread authority. No raw state/test restoration constructor is
exported.

Authenticated status uses the typed V3 codec and compares actual full scope,
ready, provider, enrollment and authority with the packet/installed binding.
The V2 status parser is incompatible with this schema. Matching unchanged
validation/observation/reply payloads use the existing V2 production oracles.

After validation, actual workload create/bind/admit-assignment/begin-prepare
are reused. Every successful returned store is retained in the same actual root
before checking post-retain errors. The actual prepare reply is decoded by the
existing receipt oracle, committed by commit-assignment, then current installed
policy/clock/four grant+approval signatures and execution-ready are rechecked.
Generic retained AgentSession and preflight associations remain explicit
refusals; they cannot bypass their separate immutable authorization routes.

The exact existing HostExecuteRequestV2 is atomically published create-only at
`controller-dispatch-execute-v3/<assignmentDigest>.sdn`, bounded and read back
through the same owner journal. Only a positive first publication can begin
execute, in the same call which consumed the authenticated prepare proof.
Existing equal bytes refuse resend; conflicting bytes refuse. Publication or
readback uncertainty records Unknown. A crash after publication but before
send sacrifices launch availability in favor of inspect-only recovery.

Reopened/resume routes with an existing execute archive or committed assignment
use inspect only. Original source is decoded and matched to canonical intent,
operation and execution; refreshed grant bytes are never used to regenerate the
original request digest. Missing original source is an explicit Unknown refusal.
Explicit inspect/progress/cancel loads the retained assignment/packet through
the actual Controller root. No control path sends execute.

Authenticated pending execute/inspect/progress/cancel advances only to progress
after consuming its one-use proof. A bounded caller may close local resources
while keeping the last exact pending response/archive for later explicit
inspect. No actual exchange cancellation error is suppressed, including when a
last authenticated pending response exists: the lower first-error API cannot
prove that a subsequent socket-close error was absent. Pending response DATA
remains available, but cancelled/uncertain cleanup remains nonzero. Actual lower
Unknown is retained. Missing exchange owner with completed=false explicitly
refuses. Local cancellation does not issue remote cancellation or erase pending
history. Actual post-send failures preserve Unknown and do not
trigger automatic execute resend. Remote cancel requires the explicit control
action. Service-stop obtains authenticated typed status/current scope first,
then sends exact same-reader/incarnation stop in that proof-consuming call.

## Authored pure scenarios — all NOT_RUN

Existing `controller_container_{wire,authority,renew}_fixture_v2` fixtures reuse
actual canonical codecs and pure Ed25519 frame construction. Their Windows
request body is explicitly common-wire DATA, not native provider admission.
No actual root, journal, reader, socket or one-use proof is fabricated here.

1. Exact canonical typed V3 status association.
2. Restarted incarnation, provider generation and service scope refusal.
3. Unready/provider/enrollment-authority substitution refusal.
4. Stable assignment archive key despite refreshed signed grant bytes.
5. Original execute digest preserved despite different refreshed proof bytes.
6. Changed immutable execution and malformed original archive refusal.
7. Actual Unknown/cancelled lower close facts remain nonzero for prepare, cancel,
   status, validate, execute and service-stop.
8. Canonical pending reply DATA cannot erase cancellation/Unknown in the actual
   cleanup disposition rule; no handle or private state is constructed.
9. Missing exchange carrier without completion refuses; Unknown survives later
   cleanup and lower Unknown without an explicit error is still nonzero.
10. The production checked revision decision consumes equal revisions and
    refuses copied earlier/invalid revisions, without fabricated registry handles.
11. Checked ceiling never wraps and permits cleanup-only use at the ceiling;
    this pure rule is not proof of an actual live owner's origin or custody.

These assertions exercise production pure helpers; they do not certify native
ownership, signature admission at a real current clock, proof-consumption
affinity, actual Host execution or cleanup correctness.

## Actual installed qualification procedures — NOT_RUN

1. Use the lead's installed Controller-root and live Host fixture with genuine
   protected setup publication. Route status through the actual command and
   finalizer; compare typed scope/provider/enrollment/authority and ready with
   real producer records. Verify one Controller writer and no client Host writer.
2. Submit a genuinely current four-signature packet for a real Windows provider
   request through dispatch begin/step. Observe authenticated status, validation,
   assignment WAL transitions, prepare receipt, fresh authorization/readiness,
   atomic exact execute archive and actual execute. Preserve all native receipts.
3. Copy a yielded exchange/phase under controlled trusted-source testing. Advance
   one canonical copy; then try the prior copy. The actual consumed proof must
   refuse without another next-phase send. Fault between take/archive/next begin
   must terminate; a phase boolean must never grant execute authority.
4. Interrupt immediately before/after exact execute publication and during send.
   Reopen the real Controller root and use explicit inspect. Existing equal archive
   must never resend execute; conflict/missing archive remains refusal/Unknown.
   Use native traces to establish no second create/start, not a DTO comparison.
5. Exercise genuine authenticated pending progress with bounded CLI polling.
   Close locally, verify socket→reader→Controller root order and retained exact
   pending data. Later explicit inspect/progress/cancel must bind original digest.
   Disconnect/local close alone must not cancel the Host or retry execute.
6. Induce actual socket/selector/current-policy/retention failures after send and
   native partial cleanup failures. Preserve Unknown, first error and every
   returned owner. Consumed-close uncertainty must remain nonzero after cleanup.
7. Run actual service-status and service-stop via installed local Windows route.
   Check same authenticated incarnation/current scope, real Host quiesce/stop
   guards, MAC reply/drain and late cleanup errors. No fake packet/UID may supply
   lifecycle authority; no claim of cross-host access follows from local success.
