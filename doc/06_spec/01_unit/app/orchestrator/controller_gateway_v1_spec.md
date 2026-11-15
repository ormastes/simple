# Typed selected-server controller boundary

Source: [controller_gateway_v1_spec.spl](../../../../../test/01_unit/app/orchestrator/controller_gateway_v1_spec.spl).
Manually authored companion; NOT_RUN. No docgen or runtime evidence is claimed.

The installed gateway policy selects a controller root, identity and allowed
actions. A client selects a server, encodes one request and correlates its frame
with the request UID and exact payload digest. An authenticated SSH connection
does not grant permission to select another controller or administrative action.

## Manual flows represented by the assertions

1. Read the quoted user HOST CONFIG schema and `server_config` path exactly
   once from `host_config`. An unrelated section's reference cannot replace it.
   Reject a foreign explicit schema and nontext or relative endpoint paths.
2. Encode and decode the typed inspect identity, then admit only an installed
   action and exactly correlated frame. Reject foreign controller identity,
   denied action, substituted request ID, unused request fields and a
   wire-selected filesystem root.
3. Require the immutable source digest for cancellation. Reject malformed
   remote success and cancellation replies with the wrong controller or UID,
   even when the outer transport frame is correlated.
4. Carry a signed execution packet to the existing domain owner without
   claiming its admission. The source's deliberately invalid packet/private
   state must fail there. Preserve legacy local argument validation and reject
   duplicate or administrative gateway policy actions.

## Full identity receipt and upload binding

The composed regression lives in
[host_identity_exchange_v1_spec.spl](../../../../../test/01_unit/app/orchestrator/host_identity_exchange_v1_spec.spl)
and its [manual](host_identity_exchange_v1_spec.md). It passes an identity upload
through this gateway's response normalizer and the exchange validator. The
normalizer preserves the full validated pending-grant receipt, including sync
fields, rather than reducing it to a public key. A direct gateway response
whose `clientPublicKey` differs from the original uploaded key must return
`controller-identity-upload-mismatch`. This is source-level composed coverage,
not a successful upload or store-publication receipt.

REQ-002/003/004 are traced at these host-config, request, policy and response
boundaries. Neither a correlated frame nor a pending-registration response
grants controller or uploaded-key authority.

These scenarios do not establish successful live SSH, container reachability,
signed execution completion, cross-host throughput or cleanup under native
failure. Those require the admitted runtime and real installed endpoint.
