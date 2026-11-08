# Authenticated smux runtime binding capability boundary

Source: `test/03_system/app/llm_caret/feature/smux_runtime_binding_capabilities_spec.spl`.
Status: authored companion manual; execution and docgen UNRUN. This is a
capability-boundary-only change. Full runtime binding remains incomplete.

REQ-SMUX-RUNTIME-BOUNDARY-001: existing trusted-local-owner token authentication
must precede capability and bind command dispatch. The unauthenticated direct
remote dispatcher must not expose these negotiated routes.

REQ-SMUX-RUNTIME-BOUNDARY-002: authenticated capability negotiation reports
the text compatibility transport with binding and framed CoreMux unavailable.
Authenticated bind requests report unsupported, committed false and streamOwned
false without changing session registry or configuration revision.

1. Reject missing, wrong or empty credentials for capability and bind requests.
2. Decode the authenticated capability reply as bounded strict SDN and verify
   every advertised field, including both explicit false capability flags.
3. Refuse exact and payload-bearing bind commands, including repeated requests,
   while preserving registry count and configuration revision/epoch/validity.
4. Verify direct remote dispatch does not gain a structured runtime route.
5. Preserve oversized and multiline frame rejection before command handling.

No provider stream owner or runtime identity is installed by this protocol.
There is no success path, fake transport, stream grant or helper process.
The existing hosted smux client's generic authenticated request can consume
the capability query; this does not advertise a full CoreMux provider.
