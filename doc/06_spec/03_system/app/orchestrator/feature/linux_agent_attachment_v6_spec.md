# Authenticated V6 signed Linux attachment

Source `test/03_system/app/orchestrator/feature/linux_agent_attachment_v6_spec.spl`.
Status `AUTHORED_NOT_RUN`.

Use an installed, reconciled Linux Host with the V6 listener, a pinned
native Podman runtime and an authorized agent held at its running stage.
Use a dedicated agent that remains running through the attachment trial.
The signed attach plan must bind the exact runtime and real smux pane.
Keep the approval, helper grants, epochs and deadlines valid for the entire
trial.

Prepare the fixture through the same `host-authenticated-service` instance
that will handle the test's attach and read requests.

1. Drive the admitted agent to a held running container and retain the exact
   canonical invoke frame for that operation.
2. Use authenticated V6 `host-control` with subaction `agent-pane-target`, the
   held operation ID, and the original invoke frame. Through a configured
   controller gateway, opt in to `agent-pane-target`, use the operation ID as
   `requestUid`, and place the canonical `host-control-sub` envelope in
   `source`. Decode the receipt and verify its operation ID and the SHA-256 of
   the original invoke frame. The Host allocates vacant pane metadata in its
   own smux registry. Repeat the exact request before attaching to confirm the
   retained receipt.
3. Request `agent-runtime-inspect` through the retained Controller with the
   same operation ID and exact invoke frame. The reply is the first retained
   running observation for the workload's native epoch scope. Use it to pin
   the native ID, execution plan and provider identity in the attach plan.
   The authenticated status still identifies the service's separate scope.
4. Construct the canonical pane binding with the receipt's session, window and
   pane IDs, Host continuity ID and native epoch generation. The receipt's
   `serviceIncarnation` names the Host continuity ID. The authenticated
   request instead uses the listener incarnation published by the ready
   reader. Have the designated authority sign the exact attach frame and then
   sign the detach frame against its digest. Keep the target vacant until the
   test attaches.

Provide the six-field pinned ready-reader fixture in
`SIMPLE_LINUX_ATTACH_V6_READY`. Its fields are `setupPath`, `setupDigest`,
`hostDeploymentRoot`, `hostAuthorityDigest`, `expectedScopeDigest` and
`expectedEnrollmentDigest`. Also provide file paths for
`SIMPLE_LINUX_ATTACH_V6_ATTACH`, `SIMPLE_LINUX_ATTACH_V6_INVOKE` and
`SIMPLE_LINUX_ATTACH_V6_DETACH`. The attach and detach files hold the signed
frames. The invoke file holds the original canonical frame retained for the
held agent. This scenario requires the prepared native Linux fixture and has
not been run.

1. Request the vacant pane target twice before attach. Require identical
   receipts, the exact held operation and invocation digest, and the same
   Host continuity ID, native epoch and pane IDs as the signed binding.
2. Refuse an authenticated attach request carrying another operation ID and
   confirm unchanged attachment state. Admit the signed attachment and drive
   the real agent with its immutable invoke frame until the exact attachment
   has live terminal authority.
3. Claim the signed smux pane over the authenticated V6 route. Repeat the claim
   and require byte-identical receipts. Take the stream epoch from the claim
   receipt, including epoch zero when the native pane starts there.
4. Submit read 1 with the wrong operation and with the wrong binding, then
   submit read 2 ahead of the cursor. Require the specific refusal for each
   request, then read successfully with the signed operation and binding at
   read ID 1. Decode the receipt and check operation,
   binding, attachment digest, epoch, read ID and payload digest. The native
   read may contain no stdout bytes. Retrying read 1 returns an identical receipt.
5. Complete read 2 and verify its receipt with the same stream identity.
   Replaying read 1 must report `runtime-agent-pane-replay-gap`. Retry read 2
   and require the original receipt again.
6. Detach using the separately signed request. Require the same attachment to
   return with its detach digest and with terminal authority removed. Close
   the client exchange and ready reader.

A failed trial can leave held Host state for the installed owner to reconcile.
