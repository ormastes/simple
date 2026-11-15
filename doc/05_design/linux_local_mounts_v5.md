# Linux local mount request V5 groundwork

Status: AUTHORED_NOT_RUN. This slice preserves requested mount metadata and
rejects unsupported execution; it does not implement workspace launch or the
Caret common Container API migration.

`LinuxOciRequestV1.mounts` reuses `ContainerMountProjectionV2` as a non-authoritative
host-root, guest-root, read-only triple. Nonempty mounts select request digest
and retained record version 5. Empty mounts add no serialized fields or digest
bytes: V1–V4 encoding and selection remain unchanged. V5 explicitly carries
terminal/user/containment fields, including their default values. Canonical
decoding requires 1–64 mounts, exact keys and types, matching request digest,
and byte-for-byte canonical re-encoding. The digest binds mount order, exact
source/destination bytes, and read-only mode. The existing command/argv,
environment, limits, and user/containment identities remain bound.

The provider validates canonical absolute path spellings, bounded count/size,
delimiter/control rejection and disjoint guest destinations. New mounts cannot
mix with legacy bundle or build roots, whose established behavior is retained.
No lexical check establishes admission. The common request projection reports
`has_workspace` for nonempty V5 mounts so resource/authority accounting cannot
classify them as workspace-free.

Execution is deliberately unavailable: provider validation, direct create
command construction, and the final executor reject nonempty mounts with
`linux-mount-native-admission-not-installed`. Action projection already calls
provider validation and therefore cannot expose executable argv for V5 mounts.
The separate exec adapter rejects V5 mounts before beginning its engine owner;
known-birth inspection and cleanup retain their existing validation routes.
Create/replay cannot silently drop mounts, elevate privileges, or fall back to
legacy roots. There is no new public mount-to-CLI argv function.

The missing capability is an actual protected filesystem owner that carries
authorized source-object identity and containment through Podman's later
pathname reopen. A preflight `stat`, no-follow fd, lexical root prefix, or
caller-provided boolean does not close that race. Existing build roots delegate
source ownership to Host and do not supply this new general mount contract.
Astra design consultation found no qualified existing owner to reuse. Native
effect support requires separately reviewed owner/admission wiring; this slice
does not invent an FFI, grant verifier, policy factory, or authority bypass.

Owned source: Linux request, retained codec, local mount validation, common API
Linux adapter projection, and Linux runtime rejection gates. No machine-authority,
service-domain, Windows, Caret wrapper, or shared-contract edits.
