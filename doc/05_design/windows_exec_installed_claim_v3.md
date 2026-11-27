# Windows exec claim through installed-state access

The claim consumer retains one mutable `ContainerExecStateAccessV3`. The Host
composition above a verified unique Windows deployment and completed installation
produces actual access. The provider does not import Host orchestration, native
file ownership or paths. This removes the provider-to-Host dependency cycle and
the previous per-helper-root namespace selection.

The lower namespace key binds full host scope and child operation ID. Immutable
record content additionally binds the installation artifact, deployment claim,
original exec intent/request, baseline and control pins, helper template and
exact query. Requests with different argv, environment or helper attempts collide
in the same namespace and refuse; there is no old-root migration or deletion.

Create and start transition to reserved only after successful nonreplacing
publication and exact readback. Any error retains the updated access and unknown
outcome. A synthetic birth argument is never a native observation: the eventual
broker must supply the actual Engine response under retained verified authority.
Closing this owner releases persistence handles only, not exec charges.

This source slice does not enable Engine effects. The public Engine exchange
remains GET-only. A copied claim phase or trait implementation is not an effect
capability. The actual broker must consume its native one-use continuation,
verify Host delegation against protected installed policy, and check admission
expiry immediately before submission. Input and geometry require their distinct
current authenticated controls and exact primary/exec targets.

The scripted lower-port integration cases exercise the actual persistence state
machine without pretending to prove native atomicity. Actual deployment cloning,
concurrent broker publication, crashes, native ACL failures and Windows resource
cleanup remain qualification gates. No Windows or compiler execution was run.
