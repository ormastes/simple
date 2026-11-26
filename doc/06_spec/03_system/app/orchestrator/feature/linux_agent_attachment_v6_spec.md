# Authenticated V6 signed Linux attachment

Source `test/03_system/app/orchestrator/feature/linux_agent_attachment_v6_spec.spl`.
Status `AUTHORED_NOT_RUN`.

Use an installed, reconciled Linux Host with the V6 listener, a pinned
native Podman runtime and an authorized agent held at its running stage.
Use a dedicated agent that remains running through the attachment trial.
The signed attach plan must bind the exact runtime and real smux pane.
Keep the approval, helper grants, epochs and deadlines valid for the entire
trial.

Provide the six-field pinned ready-reader fixture in
`SIMPLE_LINUX_ATTACH_V6_READY`. Its fields are `setupPath`, `setupDigest`,
`hostDeploymentRoot`, `hostAuthorityDigest`, `expectedScopeDigest` and
`expectedEnrollmentDigest`. Also provide file paths for
`SIMPLE_LINUX_ATTACH_V6_ATTACH`, `SIMPLE_LINUX_ATTACH_V6_INVOKE` and
`SIMPLE_LINUX_ATTACH_V6_DETACH`. These hold the exact canonical signed frames.
The invoke frame must be the one already retained for the held agent. The
detach frame binds the exact attachment digest.

The case refuses an authenticated request carrying another operation ID,
confirms unchanged attachment state, admits the signed attachment, and drives
the real agent with its immutable invoke frame. It requires live terminal
authority for the exact attachment. The separately signed detach must return
the same attachment with its detach digest and without terminal authority.
The test closes its client owners. A failed trial can leave held Host state
for the installed owner to reconcile. Pane input/output requires a separate
attachment data-path trial.
