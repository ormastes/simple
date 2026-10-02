# Shared-cache canonical root admission is not yet qualified on Windows

Status: **BLOCKS cross-host deployment**; found while resuming the native cache
acceptance lane. This is source evidence, not a completed exploit or host test.

`src/runtime/runtime_native.c:12155`, `rt_path_absolute`, uses `_fullpath` on
Windows and `realpath` on POSIX. `_fullpath` makes an absolute lexical path; it
does not resolve directory handles to their physical targets. The production
`src/lib/nogc_sync_mut/storage_roots/path_policy.spl` commentary instead assumes
Windows canonicalization returns an extended-length resolved path. Its
containment check therefore does not establish the advertised physical root
identity with the native C runtime.

Separately, `src/compiler/00.common/cache/phase_compatibility_path_io.spl`
rejects all Windows hosts before canonical directory admission. SOSIX capacity
receipts bind process memory boundaries; their Linux cgroup descriptor identity
does not supply filesystem root identity for cache directories.

Consequently two different private/shared path strings cannot prove different
storage. Lexical case/separator normalization and containment reject obvious
nesting. No-follow classification of every existing ancestor additionally
rejects symlinks and Windows reparse/junction nodes. Neither proves non-overlap
through SUBST, mount or bind-mount aliases.

The native cache fixture now performs those available defenses but must not
advertise full canonical non-overlap. Qualification needs a production owner
that obtains stable directory identity from opened descriptors/handles, checks
ancestry and rejects unsupported alias forms, with replacement revalidation.
On Windows this should bind volume/file identity and a handle-resolved path;
on Linux device/inode plus the admitted mount/ancestry relationship. Reuse the
existing `DescriptorFileIdentityV1` contract rather than inventing another
identity record. Existing SOSIX file-open support must be proven for directory
handles; a ordinary file descriptor probe is insufficient.

Required native cases on each host: distinct siblings accepted; equal/nested
roots rejected; symlink/junction and same-target aliases rejected; mounted or
SUBST alias rejected or explicitly unsupported; root replacement rejected;
valid cache publication unchanged. Until then preserve the shared root and
report deployment BLOCKED rather than treating a root string as authority.
