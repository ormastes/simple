# Enrolled primary connection policy

Status: **NOT_RUN**. Requirements: HOST-01, MUX-02.

Source: `test/02_integration/lib/host_primary_connection_policy_v3_spec.spl`.
This is an authored manual, not generated execution evidence.

## Fixture

Requires a qualified Windows runtime, the Host V3 foundation, a real Windows
Docker process-isolation engine, and the existing
`SIMPLE_WINDOWS_DEPLOYMENT_PRIVATE_PARENT` deployment fixture. Its protected
`broker-policy.sdn` must contain the existing strict version-1
`smux-runtime-control-policy` schema. The existing fixture signs enrollment
over the exact installed policy bytes. Missing prerequisites fail the cases;
they do not produce a skipped or simulated pass.

## Cases

1. Open a real enrolled host owner; obtain current protected broker bytes and
   load the V5 policy. Close the owner and compare principal, rights and lease
   bound with the existing strict decoder's projection of those exact bytes.
2. Copy the actual owner, close its native deployment/store, and require both
   the lower byte loader and the V5 policy loader to reject the stale copy.

The lower loader revalidates the native journal/deployment generation and
current host projection through `current_v3`; it accepts no request policy or
path. The app layer reuses the existing decoder. Linux direct V5 loading is
unsupported; its existing V4 route is unchanged.

These cases do not qualify input delivery, lease renewal, provider geometry,
concurrent revocation or the full V5 service. Those require independent
integration evidence. No tests or native builds were run for this change.
