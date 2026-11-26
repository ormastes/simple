# Authenticated V6 signed Linux attachment

Source `test/03_system/app/orchestrator/feature/linux_agent_attachment_v6_spec.spl`.
Status `AUTHORED_NOT_RUN`.

Use an installed, reconciled Linux Host with the V6 listener, a pinned
native Podman runtime and an authorized agent held at its running stage.
Use a dedicated agent that remains running through the attachment trial.
The signed attach plan must bind the exact runtime and real smux pane.
Keep the approval, helper grants, epochs and deadlines valid for the entire
trial.

**Fixture provisioning is blocked on the V6 listener.** The pane must be
created in the process-local smux registry of the same `host-authenticated-service`
instance that handles the attach and read requests. The configured owner
command `smux --request 127.0.0.1:PORT TOKEN create-runtime-target-v3 NAME`
can create a vacant pane and report its service incarnation, session, window,
pane and epoch. That command belongs to the configured runtime-owner listener.
The authenticated V6 listener rejects that protocol and provides no equivalent
pane creation action. A second listener owns a separate registry, so its pane
cannot satisfy this fixture. Begin signing the attach and detach frames only
after the installed V6 owner can allocate and report its own vacant pane.
Sign the pane binding with the retained Linux Host's continuity ID and native
epoch generation. The V6 pane check uses the Host continuity ID to verify the
signed binding against the local pane registry. The authenticated request
envelope uses the separate listener incarnation published by the ready reader.

Provide the six-field pinned ready-reader fixture in
`SIMPLE_LINUX_ATTACH_V6_READY`. Its fields are `setupPath`, `setupDigest`,
`hostDeploymentRoot`, `hostAuthorityDigest`, `expectedScopeDigest` and
`expectedEnrollmentDigest`. Also provide file paths for
`SIMPLE_LINUX_ATTACH_V6_ATTACH`, `SIMPLE_LINUX_ATTACH_V6_INVOKE` and
`SIMPLE_LINUX_ATTACH_V6_DETACH`. These hold the exact canonical signed frames.
The invoke frame must be the one already retained for the held agent. The
detach frame binds the exact attachment digest.

1. Refuse an authenticated attach request carrying another operation ID and
   confirm unchanged attachment state. Admit the signed attachment and drive
   the real agent with its immutable invoke frame until the exact attachment
   has live terminal authority.
2. Claim the signed smux pane over the authenticated V6 route. Repeat the claim
   and require byte-identical receipts. Take the stream epoch from the claim
   receipt, including epoch zero when the native pane starts there.
3. Submit read 1 with the wrong operation and with the wrong binding, then
   submit read 2 ahead of the cursor. Require the specific refusal for each
   request, then read successfully with the signed operation and binding at
   read ID 1. Decode the receipt and check operation,
   binding, attachment digest, epoch, read ID and payload digest. The native
   read may contain no stdout bytes. Retrying read 1 returns an identical receipt.
4. Complete read 2 and verify its receipt with the same stream identity.
   Replaying read 1 must report `runtime-agent-pane-replay-gap`. Retry read 2
   and require the original receipt again.
5. Detach using the separately signed request. Require the same attachment to
   return with its detach digest and with terminal authority removed. Close
   the client exchange and ready reader.

A failed trial can leave held Host state for the installed owner to reconcile.
