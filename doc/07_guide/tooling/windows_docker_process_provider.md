# Windows Docker process-provider integration

Status: AWAITING_VERIFICATION. There is no qualified Windows runtime result.

Use the Windows provider's typed request and explicit policy. Its host kernel and
image OS-version strings must exactly match the selected observed pair; choosing
a compatible pair remains the deployment owner's responsibility. Pin Docker's
absolute executable, local named pipe, engine identity, immutable image reference
and image ID. The provider invokes native bounded capture with a minimal child
environment and never invokes a command shell.

The caller owns a durable per-attempt journal. Persist the original request and
prepared intent before create and retain the exact returned native ID before
start. A response lost after create leaves an uncertain attempt; do not recreate
it, search by name, or prune. Recovery needs the exact native ID and validates all
ownership labels against the original request. Failure to inspect is not absence.

Run the provider only under the trusted controller authority. This implementation
does not make direct Docker-pipe access safe for independent untrusted clients.
No Windows variant has yet been admitted in the controller's Linux launch schema.
Mounts, broad network policies and automatic runtime installation are outside this
slice. A failure never selects Hyper-V, WSL or another engine.

Before enabling deployment, complete the Windows live test plan and the admitted
compiler/SPipe/manual gates. The historical Windows 11 23H2 / Server Core 2022
fixture is not a replacement for source-matched current evidence. Report explicit
NOT_RUN for absent fixture/compiler evidence rather than skipping into PASS.
