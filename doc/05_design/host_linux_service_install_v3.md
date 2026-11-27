# Local signed Linux Host provisioning

On the controller, run `host-linux-enrollment-issue` with the installed dispatch
root, controller identity, protected key store, protected output store,
approver identity, canonical binding file, operation ID, grant ID, and expiry
in milliseconds. The allowed expiry range is 1 to 86,400,000 milliseconds and
both role keys may impose a shorter window. Use the same trusted authority
policy and provider pin that the Host binding requires. Both keys must
authorize `host_enroll_v1` for the exact Host, principal, project, and budget.

The controller derives the enrollment operation and grant from the signed
binding fields, reuses the existing issuer and approver signing code, and
rechecks the installed controller context and current signatures before
publication. The signed credential is written to a private no-replace store
leaf derived from the controller and operation ID. The receipt identifies the
leaf, digests, and file and namespace synchronization state. Namespace
synchronization depends on the protected store platform. If the leaf already
exists, the command returns its name
without issuing a replacement. Transfer the credential from that store to the
designated fixture Host through the administrator-approved connection.

`host-linux-provision` is a local administrator command. It accepts, in order,
the canonical Linux V3 enrollment binding, signed credential, HostConfig,
engine policy, broker policy, and agent helper template files. Supply the remote
build helper template as the final argument when the binding pins it. The signed
binding identifies the protected parent. The administrator must provision that
parent, its authority policy, and the installed Linux machine profiles before
running the command.

The command reads bounded regular files without following symlinks and uses the
existing enrollment and credential decoders. The installer verifies the
operation, grant, approval, current clock, and exact input pins against the
protected parent policy before acquiring the existing fresh epoch admission.
It then compares the signed host, provider, policy, and broker reserve
against the current native epoch record. Signed usable capacity must fit
both observed usable limits. Installed startup repeats this comparison before
opening the Host journal. Provision then borrows the admission's actual
machine identity and calls the existing
signed installer. That installer owns the claim, ordered publication, and exact
duplicate checks. No separate writer or journal is created.

On return, the provisioning owner drains the installer writer, closes the
parent reader, returns the exact identity loan, and closes the machine
admission. Partial cleanup returns the outstanding owners through the existing
Host command cleanup path. An earlier failure remains a failure even when
cleanup subsequently completes. The command returns installed status only
after publication and cleanup succeed. When the installer returns publication
residue, the response includes its phase, binding digest, and candidate anchor
for reconciliation.

The published anchor is used with the existing installed-service startup path.
Provisioning and serving must run with their applicable installed native
profiles and epoch rules. The existing signed template verifier checks the
optional remote build helper template before any native admission or install
write. The installer publishes its exact bytes before the root manifest.
An exact retry checks the original file through the same writer, and startup
reverifies the installed bytes through the protected root reader. Legacy
bindings keep the original seven child records and reject additional input.

The test suite checks the real dispatcher for help and invalid arguments. Live
publication and reopening require a dedicated provisioned Linux fixture and
native qualification.

## Native acceptance fixture

Use a dedicated Linux host or guest with a root-owned
`/etc/simple/container/machine-policy.sdn` and the configured systemd supervisor
and Podman provider socket units. The installed machine policy supplies both the
fresh epoch and supervisor profiles. The native opener verifies the calling
process on its main thread as the active configured systemd service's
`MainPID`. It also checks the provider and cgroup topology and access to
the retained epoch lock under `/var/lib/simple/container`. Keep the provider
service and socket unused for the fixture's fresh epoch.

Prepare the protected enrollment parent and its `authority-policy.sdn` on that
fixture. Supply fresh controller output storage, authorized issuer and approver
keys, and an enrollment binding for the fixture's actual native identity and
provider. For this Linux provider, `nativeMachineId` is the exact 32 lowercase
hexadecimal characters from the fixture's `/etc/machine-id`, without a prefix
or newline. Build the SSpec with the qualified self-hosted toolchain, then run
the exact compiled case binary as the installed service's main process. The
ordinary native runner launches case binaries as children, so starting that
runner as the service would give the case the wrong PID. Record the build
provenance and the direct service execution separately. The fixture inputs
and expected receipts are in the
[signed provisioning SSpec manual](../06_spec/03_system/app/orchestrator/feature/host_linux_provision_startup_v3_spec.md).
