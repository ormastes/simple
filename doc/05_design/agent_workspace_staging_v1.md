# Installed agent workspace staging, first effectful slice

Status: SOURCE_AUTHORED_NOT_RUN. This slice stages actual bytes; it does not
execute Git, create a registered worktree, create/start a Container, replace the
primary executable, observe an agent, or enable terminal input.

The existing LinuxWorkspaceSourceOwnerV1 retains its original reader, storage,
quota lease, exclusion and root/parent handles. Its read-only behavior is preserved.
Mutation additionally requires the exact protected agent-workspace-profile.sdn
read through LinuxMachinePolicyOwnerV1.read_agent_workspace_profile_v1. That
reader is a separate accepted dependency, not a caller path or profile DATA.

Mutation additionally compares the actual retained root dev/inode with the LIVE
native storage receipt, and compares the original retained parent’s no-follow
named child with that held root. The bracket runs before effects and again before
staging success; independent successful pathname samples cannot admit nativeA /
retainedB. This correction is chronological source round4 (mutationR2), preserving
the immutable first mutation candidate and prior sourceR1/R2 history.

The new profile binds machine/workspace profile hashes, protected source asset
root, repository/full commit OID/object format, canonical finite source manifest,
bootstrap/Git/agent main-image digests, bootstrap and agent program paths, exact
image/config identity. Source and writable destination cannot overlap. The first
bounded profile supports 1–32 loose Git object files, <=1MiB each and <=8MiB total.
Packs/indexes, hooks, config, aliases, alternates and arbitrary refs are refused.
This is an administrator-attested object snapshot, not a fabricated Git checkout.

The common manifest has no execution grant or raw descriptor. It does not embed
the outer invocation digest. The full signed invocation embeds the canonical
workspace manifest; exact bootstrap argv binds the outer digest. Host verifies
both actual signature pairs, installed policy, TaskUse/desired source/catalog,
opaque selected provider intent, archive and fresh capacity begin through its
SAME actual domain before calling stage. Capacity-begin failure, including
uncertain post-WAL errors, prevents staging. No public boolean grants mutation.
The lower library has no orchestration import or duplicate proof registry.

agent_invocation_projection_v1(request_bytes, workspace_manifest, invocation_digest)
derives resource/request identity from actual current source custody and installed
profile. agent_invocation_program_match_v1 additionally checks the actual selected
agent program/config identity. stage_agent_invocation_v1 adds full canonical outer
invocation bytes, verifies their bounded SHA256, and returns the same source owner
with error/effect_attempted/ready. Here ready means only staging-complete.

Before its first possible write, the canonical source slot fixes manifest,
invocation and installed profile bytes plus an explicit operation path inventory.
Exclusive mkdir/openat operations use the ORIGINAL retained root. Descendants
are no-follow/private; successful creations retain parent/child inode identities.
Source reads hold one bounded regular file, reject hardlinks and identity/revision
changes, and compare actual bytes with approved SHA256/size before destination
write. Destination files are exclusive, mode0600, sync checked and independent
inodes. Private home/XDG/cache/tmp/worktree directories are mode0700. Full outer
invocation.sdn is published last under the original root, excluded from the
object manifest to avoid a digest cycle. No provider secret is staged here.

The same canonical slot holds all progress. A successful retry retains its existing state but refuses to reassert bytes-ready
without a dedicated retained-artifact revalidation operation. Changed invocation/
profile/request and uncertain/in-progress retries cannot repeat writes. Failure retains original source custody and all
partial files. The creation plan remains even if an effect cannot be identified;
unknown artifacts are quarantined, never treated as owned removable paths.
Generic close refuses to release root/exclusion after potential mutation.

Separate signed cleanup must still be implemented in the actual Host chain. It
must consume the canonical creation inventory and retained identity, reject
unprovable partial identity, verify actual contained-task absence and dirty/retain
policy, and use anchored exact-identity deletion. This slice intentionally performs
no recursive deletion or native quota release. It is incomplete production work,
not a cleanup success placeholder.

Real contained Git bootstrap using pinned V4 ProcessGroup, child retirement,
worktree HEAD/common-dir validation, credential projection, retained current-
process exec, original-subject executable observation and Windows equivalents
remain separate required slices. CPU-only execution guards and current provider
workspace rejection remain effective; a staging result cannot override them.

Inherited source owner history is R1→R2, two frozen rounds and one corrective batch
before merge9451. The first new mutation candidate is preserved as R1; current R2 corrects the
reviewed native/retained root mismatch (chronological source round4), not a history
reset. The identity feature's exhausted6/6 implementation is untouched. Native
and compiler campaigns remain prohibited. Specifications and manuals are authored
but execution/docgen/coverage/production qualification are NOT_RUN.
