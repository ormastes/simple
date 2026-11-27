# Retained Windows deployment provenance

Status: scoped source implementation and reviewed authored specifications.
All six pure and five native Windows cases are **NOT_RUN**. No compiler,
bootstrap, native campaign or Windows link qualification was attempted.

This owner proves an installed deployment role, not service readiness. It does
not measure physical capacity, enforce a broker job/cgroup, mint a service
epoch, reconcile inventory or a journal, prove boot continuity, or authorize an
execution lease. Signed config CPU/memory ceilings remain physical intent and
must equal the binding's physical values. A later qualified capacity owner
subtracts the signed broker partition exactly once and verifies enforcement.

`HostWindowsDeploymentAnchorV2` comes only from trusted process-installed
configuration. Its selected machine parent and public policy hash must equal
the signed `HostServiceEnrollmentBindingV2`. Neither a wire packet nor a generic
`WindowsPrivateRootV1` supplies deployment authority. The producer opens that
actual native-private parent, retains its exact public-policy file, validates
all four raw metadata hashes and the physical config, and performs complete SDK
dual-role enrollment verification before its first common Container observation.
The common Windows-only observation independently compares actual machine and
provider identity. It is diagnostic data, including the weak boot counter,
and is not converted into native boot assurance. There is no engine fallback.

Each caller text is bounded to one MiB before UTF-8 byte-array allocation. The
native files use the same one-MiB quota and exact UTF-8 roundtrip. Metadata uses
the landed pure decoder and fixed names `authority-policy.sdn`,
`host-config.sdn`, `engine-policy.sdn` and `broker-policy.sdn`; no POSIX policy
loader or path reopen of the child is used.

Creation is finite, exclusive and immutable:

1. Complete pinned metadata/config validation, fresh SDK signature checks,
   actual common observation, another native-clock SDK verification, canonical
   serialization and native nonce acquisition before the claim boundary.
2. Publish `host-claim-SHA256(nativeMachineId).sdn` with no replacement in the
   retained configured parent. Its canonical V2 claim contains kind/state,
   machine parent/native machine, operation/binding/credential digests, a native
   64-hex nonce, direct child `host-root-<nonce>`, exact derived root path and
   actual SDK `authorizedAtUnixMs`. It is never overwritten or migrated.
3. Exclusively create that direct child through the retained parent capability.
   Publish its four pinned metadata files, exact canonical signed binding and
   enrollment credential through native private staging/seal/readback/no-replace.
4. Observe the actual machine/provider again and refresh SDK verification.
   Publish `host-root.sdn` last. This enrolled manifest binds the claim name,
   exact claim digest, parent/root/child/nonce, operation, binding and credential
   digests, and its own original SDK authorization time. It is not a runtime
   ready marker or an execution journal.

The full SDK verifier runs again after expensive staging/readback at both claim
and final-manifest publication. Native root/file checks precede a final actual
clock sample and existing pure grant/approval/protected-key expiry checks. The
publication IO turn carries that last accepted sample forward as the next
clock floor; final authorization advances the floor before encoding its marker.
Regression below any accepted floor refuses before publication. Original
record times are never rewritten after staging or restamped during replay.
These are finite boundary checks, not an atomic kernel deadline guarantee or a
measured whole-enrollment time bound.

Reopen accepts the same trusted anchor and expected binding, derives the fixed
claim name and opens only its exact direct child. It scans no directory. It
requires the complete canonical claim/manifest correlation, retained binding
and credential, all four raw pins, controller/physical config matching, full
historical SDK verification at the retained positive authorization time, and
current actual common machine/provider observation. That recorded time must
not be in the future. Completed enrollment may outlive its grant; historical
verification creates no fresh operation authority. Partial or changed records
are not adopted. A copied private tree rebound to another parent still lacks
the required newly signed payload and cannot become a deployment owner.

The opaque owner retains nine sealed/read-only native file generations and two
native roots: parent policy, claim, four child metadata files, binding,
credential and manifest; roots are parent then direct child. The native child
duplicates its retained ancestor HANDLE chain. Data-only accessors expose
binding/metadata snapshots, never a generic root or serialized role token.
Any later fixed `exec-control-v3/<scope-fence>` port must independently recheck
retained root/claim provenance and preserve typed cleanup. That lower capability
bridge is not implemented here; it must avoid a Container-to-orchestration cycle.

`HostWindowsDeploymentCleanupV2` wraps the existing files-first/reverse-roots
native cleanup plus optional residue. Residue survives every failed close and
records claim/root attempts conservatively, including unknown final-manifest
publication. Closing handles never deletes/releases a durable machine claim or
grants permission to allocate a replacement. Preclaim owner-free errors reject;
retained native resources return CleanupRequired; incomplete/unknown publication
with closed handles returns RecoveryRequired. No rollback, claim deletion,
automatic adoption, raw enrollment-lock change, or second WAL is introduced.

Primitive source dependencies are the landed native Windows private owner
`635294131cca3a7ff7c8fe552e566fd69e9e6e7c`, its current-root query
`eb6ab9bd17c6deba07e1a4127d344a20dc97cb58`, shared private cleanup from
`60df4d058e4`, and metadata decoder
`570ae618a5fcf49e86da6019f22f879ad7b42a08`. The actual static binding/SDK
adapter is `b52d2a4266fba4a719d955811065e2cba7e172ac` with traceability
follow-up `20f258c74bdeb8d2b52017fcb1ad53c7ba0aa467`; those two immutable
dependencies were materialized separately in this worktree. The observer is
the actual common `simple_container_observe_v2`, not the request-specific V3
exec-control session or a direct engine invocation. The reviewed common
Windows readonly checkpoint is `a58dd30d5b2f54b7b98151bde51828f9916894af`.
