# smux primary session V4

Status: consumed source implementation; runtime qualification **NOT_RUN**.
This is the smux lifecycle prerequisite for Caret integration. It does not
complete interactive controls, Caret migration, or Windows primary transport.
The subsequent input slice is described in `container_primary_input_v4.md`;
its native qualification remains NOT_RUN.

## Installed protocol

The authenticated foreground server now dispatches these explicit V4 commands:

| Command | Action |
| --- | --- |
| `runtime-primary-capabilities-v4` | Report configured planning and unavailable controls. |
| `plan-primary-runtime-v4 TOKEN` | Resolve the retained parent and archive an actual common primary plan. |
| `prepare-primary-helper-v4 UID` | Admit the protected staged signed helper request against that plan. |
| `bind-primary-runtime-v4 TOKEN` | Begin the admitted helper, open through Host, and adopt into the pane. |
| `inspect-primary-binding-v4 UID` | Observe progress and settle only with canonical cleanup proof. |
| `cleanup-primary-binding-v4 UID` | Explicitly clean the exact helper transport, then attempt settlement. |
| `runtime-primary-control-v4 TOKEN` | Use the existing issuer and explicit attempts for independent primary input or Linux container geometry. |

Discovery, requests, and replies use separate V4 SDN schemas. The request wraps
the unchanged V3 target request plus `terminalMode` (`stdin` or `tty`); its
digest binds the entire wrapper. This reuse does not change V3 output-follow
semantics or capability bytes. Primary request/plan archives have distinct
namespaces and use the existing private, no-replace publication primitive.
The existing protected helper staging location and signed proof flow are used;
the wire never supplies a signer, provider owner, execution grant, or root.

The server and request client retain their existing 4096-byte total frame
limit, including authentication and command text. The standalone codec's
4096-byte SDN / 5462-byte token bounds do not override that transport limit;
callers must fit the complete frame. Oversized requests are refused.

`inputSupported`, `geometrySupported`, and `interactive` are false in global V4
capabilities and binding replies. The separate V4 control reply can report
input only after the exact live lease is installed in the actual native gate.
The later Geometry reply requires an actual endpoint acknowledgement and current
lease; global readiness and interactive remain false. A primary plan can still be refused by the actual
provider; configured planning is not a claim of Windows attachment support.

## One Host writer and one pane reader

The existing runtime binding owner holds both entry collections and the same
latest `HostLocalRootV1`. V3 and V4 turns replace that one owner; primary entries
never retain their own Host root. Both domains share the eight-entry bound and
reject a binding UID already active in the other domain.
Inspection/recovery applies the same opposite-domain entry refusal before any
archive recovery or registration. Internal unresolved markers include the
output/primary domain: recovering one domain cannot erase the other's stop
blocker for the same textual UID, including archives from prior incarnations.
These keys are process-local; public request, reply, and archive UIDs are unchanged.
Fully released opposite-domain tombstones do not block sequential recovery.
Inspection and pruning share the same predicate: any retained helper/session,
cleanup/recovery carrier, or release/adoption flag still blocks despite a
`released` label.

`PaneRecord.owned_terminal_session` is the common tagged terminal session.
Output-follow adapters preserve existing V2/V3 behavior. Primary adoption checks
the exact pane epoch, revision, child incarnation, service incarnation, and
registry uniqueness before publishing the opaque primary session. After a
successful adoption the binding entry clears its live session. The pane keeps
the canonical session; its retained native reference supplies the existing
bounded sole-reader loop after correlation with that session. No second helper,
reader, or supervisor is created.

Generic send, paste, queued writes, terminal-generated replies, geometry,
replacement launch, and legacy close/reset cannot bypass owned-session guards.
Pane/window/session removal, split rollback, and server stop retain unresolved
owners. Stop also checks entries with pre-adoption cleanup or uncertain Host
state even when no pane owns a stream.

## Cleanup, publication, and settlement

Before adoption, explicit cleanup uses the retained Host turn. After adoption,
the pane owner cleans the actual tagged session. Host receives its updated
cleaned state for proof-only settlement through the existing journal. No route
stops or destroys the workload container. Helper/native identities remain
distinct from the provider's workload identity.

Every returned Host/capacity owner replaces the current owner. Updated cleaned
session state is published to the pane before any settlement ACK can clear it.
Publication failure retains that cleaned progress for publication retry; it is
not a second reader or permission to run cleanup independently. Adoption fields
must match exactly, and native-cleaned state cannot regress. Configuration
comparison includes the synchronized cleanup flag; rollback preserves current
pane owners rather than restoring stale authority.

Pane release requires the actual Host ACK to match the session plan, helper
native identity, and exact current adoption. Failed proof/publication/commit
keeps cleanup or capacity pending. Restart reconciliation uses the existing
metadata-only primary recovery and recovered settlement, with fresh canonical
proof; it reconstructs neither a live session nor an input grant. An exact
helper row still admitted after rejected begin remains retryable without a
permanent blocking entry; executing or uncertain rows require reconciliation.

## Evidence and remaining work

Nineteen new source scenarios cover strict codec boundaries (six), private
archive correlation and no-replace conflicts (three), unconfigured authenticated
dispatch, the existing frame bound, and unchanged V3 discovery (four), and
lifecycle guards (six).
The latter exercise the production monotonic metadata predicate and a real
signed admission/journal fixture for admitted-versus-executing retry decisions.
They also check the production pending-marker helpers in both directions:
resolving a domain preserves the other domain's identical UID and duplicate
resolution cannot clear it. These metadata scenarios do not execute native
recovery or configured server inspection.
The shared entry predicate also distinguishes a fully released same-UID
tombstone from unresolved or inconsistent released-with-retention metadata.
The existing output terminal-reference fixtures now wrap the common output
variant without inventing primary native owners.

All are **NOT_RUN** under the existing six-cycle runtime campaign cap. The
configured server's successful plan/prepare/bind, native pane adoption, sole
reader, cleanup, publication failure retention, exact ACK release, and live or
recovered settlement are **NOT_COVERED** by these source specs. The retry
predicate fixture does not execute the full failed-begin server transaction.
Performance and cross-platform behavior remain unqualified.

The subsequent primary input and Linux geometry ports consume independent
leases and native/provider fences in source. Next work must qualify those
effects, then migrate Caret's current launch and cleanup registry
through the qualified lifecycle. Windows needs its real Docker
attach broker loop. Existing Caret `--container` behavior remains in place.
