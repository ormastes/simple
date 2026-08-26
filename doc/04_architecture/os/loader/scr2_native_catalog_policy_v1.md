# SCR2 Native Catalog Policy v1

`SNC2` is a canonical policy signing body and `SNE2` is its boot-root-signed
envelope. It is a native catalog policy, not a SAM1 manifest and not a
translation layer for legacy catalog records.

Each `SNC2` row is keyed by the exact tuple `(role, authority identity,
SimpleOS target)`. It binds canonical executable path, aliases, entrypoint and
the complete executable launch template: artifact kind, ABI features, required
services and capabilities, resource ceilings, namespace, native/SMF libraries,
interpreter, argument schema, and startup preloads. No field of the projected
launch policy comes from unsigned configuration, process arguments, a path
lookup, or a SAM1 sidecar.

The independently pinned boot root authenticates `SNE2`; public architecture
adapters source it only from their compiled x86_64, AArch64, or RV64 pin, never
from media or a caller. The envelope must use
the compiled root key ID and SHA-256 identity, then verify its raw Ed25519
signature over canonical `SNC2` bytes. `SNC2` delegates exactly one 32-byte
SCR2 Ed25519 key, bound to its SHA-256 identity. The catalog owner subsequently
decodes SCR2, selects exactly one local-target row, compares the row's signed
role/authority/target/path/aliases/entrypoint to the SCR2 subject, and invokes
the existing SCR2 verifier with a singleton policy derived from that row.

The resulting `Scr2NativeExecutionPolicyV1` contains only the authenticated
SCR2 subject and authenticated catalog record. It does not open an image,
create a loader token, construct SAM1 bytes, or issue a capability. A future
boot consumer must retain its VFS observation separately and consume this
value atomically with image admission.

The codec rejects unbounded fields, nonprintable text, wildcards, invalid paths,
non-SimpleOS targets, duplicate aliases/arguments/preloads, duplicate
role-authority-target tuples, key-hash disagreement, malformed booleans,
negative limits, trailing bytes, and noncanonical encodings. Local adapter
entrypoints hard-bind x86_64, AArch64, or RV64 and cannot project another
architecture's record.

Static cases live in
`test/01_unit/os/kernel/loader/scr2_native_catalog_policy_v1_spec.spl`. They
require later self-hosted execution under the standing no-execution constraint.
