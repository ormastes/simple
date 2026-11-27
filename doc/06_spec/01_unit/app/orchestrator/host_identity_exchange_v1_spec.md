# Public identity exchange and correlated pending receipts

Source: [host_identity_exchange_v1_spec.spl](../../../../../test/01_unit/app/orchestrator/host_identity_exchange_v1_spec.spl).
Manually authored companion; **NOT_RUN**. The source composes codecs and
deterministic public-only callbacks. It does not execute SSH, publish a real
pending registration, install a pin or grant access.

## Manual flow represented by the assertions

1. Build a public identity-registration request, normalize its response through
   `controller_gateway_response_v1`, then validate the client exchange result.
   Preserve the full typed pending receipt, including `pendingGrant`,
   `fileSynced` and `namespaceSynced`; returning only the server key would lose
   operation evidence.
2. Bind a registration receipt to the public key originally uploaded in the
   request. A receipt for another uploaded key fails both the gateway path and
   the direct client callback path.
3. Accept a server-key receipt only when action, controller, request UID,
   server name, key type and recomputed fingerprint agree. Pending upload
   receipts keep authorization, enrollment and registration false and possession
   `not-proven`; these are not server grants.
4. Send only canonical public material through the callback. Preserve a nonzero
   transport reply unchanged. Reject private input and invalid references or
   options before the callback; the source includes a fail-fast callback trap
   specifically to check this ordering.
5. For key retrieval, compare the independent expected fingerprint before pin
   storage. Validate one exact known-hosts alias/key line. Reject unsupported
   gateway actions, invalid upload source and unused server-request source
   before server IO.

| Failure group | Authored rejection checks |
|---|---|
| Correlation | Wrong controller, UID, server/action, uploaded key or fingerprint. |
| False authority | Application signing-key type, private fields, authorization/enrollment/registration claims, claimed uploaded-key possession or cleared pending grant. |
| Schema | Duplicate/malformed fields and string supplied where a boolean is required. |
| Early validation | Private upload, invalid options/reference, unexpected gateway action/source and incorrect or multiple known-hosts lines. |

Requirements: REQ-002/004/006 and NFR-002/003. The composed receipt retains a
test value `namespaceSynced: false`; accepting it is not proof of namespace
durability. Actual retained-store publication, conflict handling, cleanup,
authenticated exchange, pin persistence and separate server grant still need
runtime evidence. See the [gateway manual](controller_gateway_v1_spec.md),
[identity setup](../../../../07_guide/tooling/orchestration_host_identity.md), and
[verification plan](../../../../03_plan/sys_test/server_contexts.md).
