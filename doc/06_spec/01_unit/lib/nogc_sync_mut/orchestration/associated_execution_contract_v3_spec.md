# Service intent and associated execution V3 codecs

Status: **SOURCE_AUTHORED_NOT_RUN**, new signing integration cycle 7. No compiler,
test, native, build, seed or actual Host admission was executed. This manual
describes five authored pure codec cases, not production runtime qualification.

The four new production modules follow `ASSOCIATED_API.md` agreed with the
service owner: execution_draft_v3, host_prepare_associated_v3,
host_execution_association_v3 (including prepared reply), and
host_execute_associated_v3. Existing V1/V2 codecs remain strict and unchanged.

The scope-free `ContainerExecutionDraftV3` carries backend, workload, attempt,
operation, claimed semantic request digest and exact provider request bytes.
Linux Podman is the first supported backend. Its raw body cap is 1MiB and
canonical envelope cap is 2MiB. Pure bind derives a service-intent or native
request from a supplied scope; it observes no native scope and grants nothing.
The actual provider must rederive semantic identity/resources. SHA256(raw
request bytes) is never substituted for its semantic digest validator.

`HostPrepareAssociatedRequestV3` binds the existing signed reservation request
and exact draft to a genuine stable service scope: service incarnation mode,
empty boot, exact physical/service/provider/fence identity and the derived
service-intent plan digest. That plan cannot be passed to native Create.

`HostExecutionAssociationV3` binds enrollment digest, exact service scope,
original intent digest, existing receipt.receipt_digest/prepared revision,
actual epoch-record digest, actual service-process identity digest and exact
native execution request. Native mode requires real boot/continuity equality,
the same physical/native-machine identity, and exact `epoch-<recordDigest>`
service ID. Native provider generation is the plan's exact actual generation;
it is not forced to the service generation or a made-up request counter.

`HostPreparedAssociatedReplyV3` carries prepare, receipt and association. The
Controller must receive it through the actual correlated authenticated prepare
exchange. Decoding an echoed/integrity receipt is not native admission. The Host
must publish/read back the association on its existing actual journal after
signed capacity admission and real native-owner observations.

`HostExecuteAssociatedRequestV3` carries that prepare/receipt/association plus
an operation changed ONLY from the original operation's action/payload digest:
`host_execute_associated_v3` and exact association digest. Envelope identity,
subject, project, scope, policy, budget and duration fields stay equal. The new
grant must explicitly include that action and approval must bind its exact
operation/grant digest. Actual role/signature authorization remains with the
Host owner; shape-valid signature bytes do not establish it. No old
host_execute_v1 grant or V2 packet conversion can silently stand in.

All new envelopes use exact fields, strict duplicate/unknown rejection,
canonical nested text and final LF. Escaped output size is computed before
allocating outer encoded strings. The actual transport has independent old
request 2MiB/reply 1MiB limits, which are not expanded.

The first associated route is deliberately narrower: raw draft <=8192 bytes.
`host_prepare_associated_transport_v3` must run BEFORE capacity admission or
epoch acquisition. It counts known prepare/service-scope escaping exactly and
uses conservative bounded native-plan/association/receipt/outer-auth expansion
for observations not available until prepare. It creates no fake association
for sizing. Oversize refuses before admission; supported size does not promise
admission. Final actual request/reply encoding remains independently bounded.

| Pure source case | Production rule exercised |
| --- | --- |
| Draft round trip | Exact request bytes/digest preserved; service and native generations remain distinct data. |
| Prepare/reply/execute round trip | Explicit new wire kinds and action; exact association digest bound. |
| Association tampering | Epoch service-ID relation, boot continuity, receipt digest and exact draft bytes. |
| Legacy/action/envelope tampering | Old execute grant, changed project and changed process identity refuse. |
| Strict shape/route bounds | Unknown, duplicate, noncanonical or wrong-kind input refuses; codec body support never bypasses route limits. |

The pure fixture contains literal scopes, budgets and integrity receipts and
zero-filled signature SHAPES. It is not a signer, capacity owner, authenticated
reply, real clock or native generation. No native owner is fabricated. These
data cases must never be imported as a production or genuine-system fixture.

Actual signed prepare, native association publication, real prepared reply,
fresh matching-key execute, same-ID original retry, revocation/expiry and
cleanup qualification belong to the actual installed owner/Controller fixture
and remain **NOT_RUN** here.
