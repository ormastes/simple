> Historical openerR2 design carried for traceability. Current broker authorization,
> actual installed begin, and remaining control/retirement gates are specified in
> [host_broker_authorized_recovery_v7.md](host_broker_authorized_recovery_v7.md).
> The earlier missing read-only broker selector below is implemented by that delta;
> its runtime qualification and live control remain pending.

# Protected Linux Host Agent startup

Status: SOURCE_AUTHORED_DEPENDENCY_HOLD / NOT_RUN. The actual new internal module
is `host_service_agent_installed_v7`; all public calls return or retain actual
owner capability values. The persistent service must store returned `owner` and
`local` before inspecting any error or responding. No new registry is added.
The existing Linux reader/journal health oracle and native workspace custody
remain canonical. The caller bridge in the existing service lane is a required
separate dependency; this artifact alone is not an operational service route.

`host_service_agent_installed_open_v7(root, template)` first checks genuine Linux
process origin and canonical helper template shape. The template is trusted
installed service initialization DATA, never invoke wire input; it grants no
execution. Root and machine-parent readers are the actual opaque protected
readers. Each acquisition is stored before ready/error checks; fixed enrollment,
config, policy, root/runtime-ready, exclusive claim and credential records are
read through those retained handles. The shared pre-engine validator preserves
all existing claim/enrollment/pin checks; legacy private-path acquisition still
uses its existing functions before this shared DATA validation.

No legacy Container open or engine observation occurs. The accepted public
`std.container.simple_container_open_workspace_installed_v3` acquires the original
fresh machine root and returns its actual native observation/scope. Both must
match enrolled identity/provider and the full expected scope; no relabeling,
provider replacement, managed-mode fallback or open-then-swap exists. A mismatch
retains the original workspace startup owner for real cleanup.

The new Host capacity forwarding selects ONLY actual
`distributed_operation_journal_open_linux_v3`, retaining its existing typed
open/cleanup variants. Authority digest, entropy nonce and capacity derive from
validated enrollment and the actual matched scope. Existing capacity projection,
writer oracle and execution recovery are reused. Every successful returned
journal is adopted before the next fallible operation. Legacy/Windows factory
defaults remain unchanged. No second journal writer or database is created.

Historical workload completions read receipt, exact execution packet, observation,
wait and signed cleanup intent through SAME journal `read_required_v3`, keeping
existing exact operation/plan/request/provider/native/absence/time/signature and
outcome-digest checks. Primary-connection completions reuse the existing owner-aware
validator. No completion row flag or file absence grants release. Invalid/missing
evidence stays charged/uncertain. Only when every retained row is already proven
Released may the genuine matched startup mark its projection continuous. This
supports valid historical completions as well as empty history.

REQUIRED GAP: legacy output-follow and primary-attach completions reopen external
broker roots via metadata paths. The current installed Host policy has no allowed
broker-parent/root provenance field, and no owner-bearing retained broker recovery
port exists. Archive `.launch.root` is not installed authority. These rows remain
charged pending that required implementation; this is not final recovery acceptance.

`retain_v7(owner, actual_latest_local)` validates same root/enrollment/config/policy,
scope and actual current Linux writer identity, then adopts returned capacity and
container before status/error handling. Service workflow callers must use this
with their actual returned local pair in the SAME canonical service slot. Getter
or caller DATA cannot reconstruct protected reader/storage custody.

`cleanup_v7` adopts actual lower workspace/source return before journal close,
then typed journal cleanup, parent-reader close and root-reader close. Every
partial result is stored before flags/errors. Active/staged/unknown lower custody
refuses close; no task/runtime release or destruction authority is inferred.
Nil capability with incomplete cleanup is retained as monotonic uncertainty,
preventing later false closed success or invented alias retries. `status_v7`
emits bounded canonical SDN with pending/closed/resource-retained flags and no
raw prompt/profile/credential/capability data; a Ready response checks actual
reader and journal currentness. Startup Ready means only Host admission, never
AgentObserved/input/readiness or full runtime release.

Seven unit DATA/source scenarios are AUTHORED_NOT_RUN. Real lifetime cases are
BLOCKED until the installed authenticated canonical service caller is wired.
Runtime/compiler/native/tests/docgen are NOT_RUN; coverage NOT_MEASURED. Existing
Host contextR2, SourceLoan5 and Source6 immutable bytes are not edited. This source
depends on accepted startup20R2 plus pinned UNREVIEWED Linux protected journal and
reader producer source. Nonblocking workflow/observer/attach/finalizer/probe and
service caller ownership remain separate gates; no end-to-end acceptance claimed.

## Consolidated R2 correction, same Host history

R1 receipt HOST-INSTALLED-R1-P1-01/02 required complete historical read closure
and explicit refused-input custody. R1/opener8, contextR2, SourceLoan5 and Source6
remain immutable. This is one R1→R2 source correction batch, no limit reset.

The existing child projection now branches on the actual journal backend for
child request, original parent reservation/execute packet, creation intent and
immutable observation. Protected Linux uses SAME owner `read_required_v3` or
existing owner-taking creation/observation loaders. Legacy branches retain their
prior readers and all exact operation/subject/intent/native/plan/provenance checks.
The existing no-begin chain similarly uses protected optional reads for receipt
and delegation presence and required reads for the cancellation receipt. Only
`Ok(None)` proves absence; inaccessible/substituted/oversized/corrupt reads remain
errors. The existing barrier index, historical grant/policy binding, admitted to
cancelled edge, outcome digest and ancestor endpoint checks are unchanged.

`HostAgentInstalledTurnV7` adds
`rejected_local: Option<HostAgentInstalledRejectedLocalV7>`. That opaque class
privately retains the actual incoming `HostLocalRootV1` and exposes no getter,
cleanup or execution method. Early not-live/provenance/sequence refusals return
the accepted original owner/local plus this distinct rejected-input carrier.
This retains custody without accepting mismatched authority. Matching resources
are still adopted before fallible currentness checks. The only retry forwards
that genuine private retained local through the original provenance/current gates.

CALLER PUBLICATION RULE: the canonical persistent service must store the ENTIRE
returned turn, including accepted owner/local and rejected_local, atomically
before inspecting error or publishing a response. The previous rule to replace
only owner/local is insufficient and is superseded. While rejected custody exists,
new effect/admission attempts must stop; do not overwrite or discard it with a
new incoming pair. Explicit retain_rejected retry replaces that same retained
turn; only successful validated adoption consumes its quarantine arm. Mismatch
never authorizes old-owner cleanup of the rejected resources. No forced cleanup,
capability serialization, second registry or automatic source release is added.
The actual canonical caller integration remains a required separately owned gate.

Added tests cover pure protected optional-read result interpretation (including
unknown-read negatives), complete child/no-begin source routing and refused-input
private quarantine/retry boundaries. The separate negative compile fixture must
reject external `.local` access; it is AUTHORED_NOT_RUN, not a passing test. Seven
unit scenarios and service lifetime cases remain NOT_RUN/BLOCKED; no native or
actual owner custody fixture is invented. External broker recovery remains REQUIRED.
