# Reuse of actual smux input and provider ownership

Design inventory only; no shared source edits, native commands or new exports.
Pinned fetched `origin/release/1.0.0`:
`9174bd39fc6841ba26a3f32a86d2dc1d43048e99`.

## Existing complete lower chain

The previous V4-only inventory was too narrow. Windows leaf input is not absent,
and neither is the common tagged issuer/receipt path. Current production contains:

* `terminal_primary_input_v2.spl`: actual adopted tagged gate/install/revoke,
  dispatching Linux PrimaryAttach and Windows PrimaryConnection observations.
* `terminal_primary_write_v2.spl`: actual tagged writes/observations. Request
  includes real lease/target/principal/nonce, attempt, frame sequence, payload,
  offset and maximum. Queued/Completed/Unknown and accepted prefix are preserved;
  completed native write does not mean application consumption.
* `runtime_connection_owner_v5.spl`: private retained HostServiceDomainV3, live
  issuer, actual connection tasks, adopted entries, pending exact input request,
  digest and receipt. It borrows the canonical pane session rather than opening
  another reader. Input issue checks live client attachment, target and gate;
  input write rechecks the issuer and reserves Unknown before native effects.
  Exact retries reconcile receipts; changed attempts/frames/suffixes refuse.
* `runtime_connection_dispatch_v5.spl`: typed resolve/issue/write/observe/revoke
  actions preserve that returned owner. `input-write` requires explicit attempt,
  frameSequence, data, offset and maxBytes.
* `server.spl:229–235`: the installed server dispatches the canonical
  `runtime-connection-v5` token to the existing owner and stores the returned
  owner before replying. Server polling retains native/Host progress and cleanup.
* `terminal_primary_service_v5.spl` and `smux_pane_adopt_primary_v5`: actual
  publication gives the pane sole native stream authority. Windows genuine
  HostPrimaryConnection service/consumption/settlement owners already exist.

Input, geometry and workload control remain separate authorities. Input failure
or transport retirement cannot settle a workload or release its Host charge.
Pending/unknown input prevents unsafe reissue/revoke/close through existing gates.

## Direct reference evidence and limited missing seam

At this release, static references under `src/app`, `src/lib` and `src/os/apps/smux`
to the V5 request token/dispatcher/`runtime-connection-v5` command are the request
codec, dispatcher and installed smux server. No direct Caret app consumer appears
in that bounded reference search. This says nothing about external or dynamically
constructed clients. CoreMuxV1's generic typed client exposes connect/query/
execute/poll/disconnect; its command set has no runtime-connection issuer action.
Generic pane SendLiteral/SendKeys remain guarded and cannot substitute authority.

The finite local trusted composition should consume these existing owners rather
than create another common input module, PTY, issuer, pipe or supervisor. Remote
SSH composition remains outside this slice and does not authorize raw protocols.

The current V5 `smux_runtime_connection_host_v5` owns its private Host domain, but
calls the original unconstrained Host execution begin. A separately held app
HostServiceDomain must not open the same journal or duplicate its writer. The
minimal candidate shared hook is therefore within this SAME V5 owner:

`smux_runtime_connection_host_constrained_v5(actualOwner, signedRequest,
optionalRestrictiveConstraint) -> existing SmuxRuntimeConnectionTurnV5`.

The existing function delegates with no restriction. The new function copies the
constraint, forwards to the already reviewed constrained Host begin, and includes
the exact retained restriction in same-request replay equality. Changed constraint
under the same signed operation must refuse while retaining the original owner,
not return an old unconstrained success. Existing poll/cancel/connection lifecycle
continues unchanged. A read-only scope DATA getter can derive from that retained
actual domain so the app can build a restrictive constraint without a writer getter.
Neither getter nor constraint is a grant.

The reviewer froze this bounded interface before edits to
`src/os/apps/smux/runtime_connection_owner_v5.spl`. The authored new
`provider_cli_smux_task_v1.spl` builds the same restrictive constraint through the
existing task builder, invokes that actual owner's constrained Host entry, and
delegates existing input resolve/issue/write/observe/revoke while retaining the
owner on every turn. Scope extraction in the existing task builder is restrictive
DATA reuse, not a new receipt/admission factory. It still refuses Codex stdin,
Resume and workload Interrupt. Existing input completion is never promoted to EOF.
No dispatcher/native change is needed for a direct in-process trusted composition.
A later CoreMux transport extension must
preserve current credentials, leases, request identity, bounded frames and retained
receipt semantics; it is not authorized by an arbitrary caller path or token.

## Linux and EOF limits that must remain explicit

V5 open currently calls `host_primary_connection_supported_v3`, which admits only
the genuine Windows root. Linux primary attach/input exists through the V4 binding
owner and actual Linux common leaf. The app must preserve that Linux route rather
than send Linux through the Windows V5 connection factory. A local Linux bridge
can wrap the SAME existing `SmuxRuntimeBindingOwnerV3.local` in its typed Host
domain, invoke the already approved synchronous constrained Host path, and retain
the returned actual local root before later V4 bind/input. It cannot open another
root or journal. Exact shared wrapper ownership remains a review item.

Codex's currently frozen `exec ... -` plan requires stdin prompt transport. The
bounded search of the actual common tagged input/write, Windows connection,
process facade and V5 owner found no controlled stdin EOF operation. Expanded
inspection found the separate finite-input owned process V3 start/input receipt:
its native POSIX/Windows process owner closes its own launch input after the
entire initial payload drains. That owner is not the adopted terminal lease.
`local_unix_shutdown_write_v1` operates an actual LocalUnixConnectionV1, not a
PrimaryAttach process ref or Windows named-pipe owner. Neither can be substituted
for an EOF right on the adopted controlled input session. Writing bytes
alone does not establish a complete stdin prompt transaction. Do not invent EOF
from newline, lease revocation or transport cleanup. Resolve this through actual
supported CLI prompt mode with primary-source evidence, or a reviewed existing
owned EOF producer; no new native exports are authorized. Current task consumer
therefore keeps stdin refusal. Resume still requires actual source/session custody,
and workload interruption needs its real control owner.

## Exact source consistency

All eight inspected current-release files below were byte-identical to the worker
tree; SHA256 values were read from the fetched commit:

| File | SHA256 |
|---|---|
| smux/runtime_connection_owner_v5.spl | `18e2ad940d4d3eac1119ee43ef203194a475ff1e32061f6d7a9fae4769842d84` |
| smux/runtime_connection_dispatch_v5.spl | `6f31f4efb867c5853ec853d413115100fd89bbcf36d1a81a3cb5ae985926ba21` |
| smux/runtime_connection_request_v5.spl | `903dff3b4e4e86e89b41ebe2221b70b26c90bb98f76175985fd00e47bf8fc617` |
| smux/server.spl | `a1226bbe545c3b07bd2c2840c418118c74f5ed1903d272b851ca291ccb32177d` |
| container/terminal_primary_input_v2.spl | `1ad71363411bd0db70a3065b836dece0a3a0cf106c4fad22962077975f8b4534` |
| container/terminal_primary_write_v2.spl | `8a84cd5ae16aad9d771b2a6aaa23b32f8f4f8bca5885fc0f6fa6e2ea7bffb97a` |
| mux/execution_v1.spl | `e6a33b634798b2d97b4ef2b44ce876d1231306708d6f31fc74be9b7b13628553` |
| sosix/mux/client_v1.spl | `023789111fb608d64b335f1bf3cc1d056a8ea1d72206ee9732a4e8165066172b` |

Status: design-only, AUTHORED_NOT_RUN. No new capability, native qualification,
full input delivery, app routing or feature completion is claimed.
