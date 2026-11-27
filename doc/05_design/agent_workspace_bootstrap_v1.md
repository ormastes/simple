# Single-primary Linux Git worktree bootstrap

Status: SOURCE_AUTHORED_NOT_RUN. New body, not production qualification. The
accepted source snapshots through consolidated final6 remain immutable.

The compiled profile is linux-agent-worktree-bootstrap-v1. Its immutable image
must provide /usr/bin/git and the actually empty, no-follow retained directory
/opt/simple/empty-git-template. Native workspace admission must explicitly select
this profile and verify its exact bootstrap/image/assets, rootfs, mounted-root
identity, working directory, tty and open stdin. The previous profile receives no
implicit execution support. The image/rootfs closure and native association are
separate prerequisites; this bootstrap grants no Host authority or bare-host
fallback. Initial cwd comes from the actual primary kernel cwd, which the genuine
pre-start mount/config owner binds to the installed variable guest_root.

The primary reads the fixed invocation.sdn through its retained mounted-root
handle, requires bounded regular single-link stable content, validates exact
SHA256 supplied by fixed argv, and strictly decodes the complete canonical
full InvocationManifestV2 and workspace manifest. Mandatory executable policy
binds exact image size/maximum and compiled x86_64/AArch64 ISA. Host/native
allocation checks precede this child; child numbers are mechanical bounds.
Task/inner argv are delivered as actual bytes,
not reconstructed from a digest. Fixed wall expiry and one locally sampled
monotonic preparation start bound every step; budget is not refreshed by retries.
The initial body rejects credential references before helpers because the scoped
projection producer is not implemented; it never hands secrets to Git or claims
that a reference proves authentication. This remains required production work.

Template emptiness uses the original retained directory fd, a CLOEXEC duplicate,
verified lseek-to-zero on every call, and a bounded libc directory stream. Only
dot entries followed by actual EOF mean empty. Errors consume the duplicate/stream
once, preserve diagnostic failure, and never reopen the pathname. The small
RetainedDirectoryOwner forwarding delta composes separately with the executable
replacement owner's cwd delta; the complete successor is exactly780lines against accepted execR2.

Actual Git stages use the existing sealed executable pin with digest equal to the
signed stage git_digest, an actual cwd pin and V4 ProcessGroup owner. A complete
sorted environment removes inherited configuration/loader/helper authority and
uses private HOME/XDG/temp. The primary explicitly selects umask0077 before Git;
failure cleanup restores the original mask, while successful agent exec keeps
the private default. No shell, source hook/filter/config/alternate/template, SSH
helper or network operation is invoked. Protected image contents remain outside
the writable workspace. The main-image seal/hash does not attest interpreter,
shared library, Git helper or other image closure files.

The real bounded command sequence is version, fresh bare init with fixed empty
template/object format, full strict fsck of the approved OID, commit-type check,
detached checked-out worktree creation, exact NUL worktree listing, exact HEAD,
absolute common-dir and absolute per-worktree git-dir. The initial flag-compatibility
guard accepts strict versions2.36.x–2.56.x and rejects suffixes/unknown versions;
it is not a security or native qualification claim for that whole range. The
installed policy still binds the exact approved Git digest/image and usable
contained V4 capabilities. Old fsmonitor boolean values are not executed as
compatibility hook paths.

Each Git child is an existing genuine V4 lease. Capture covers only helper
stdout/stderr; the bootstrap never drains or injects EOF into the primary tty.
Progress requires actual exec confirmation, terminal status, explicit
tree_empty/control/timing, complete EOF captures, frozen binding and matching
acknowledgement. Leader reap or freeze alone is insufficient. Unknown start/ack,
nonempty tree and unresolved cleanup retain the primary and exact owners for
genuine outer Host control; no second launch or alternate path is attempted.

After all helpers are acknowledged, retained original-root descendants verify
real .git, HEAD, commondir and gitdir files plus named-parent/held-child identity.
Only the verified checkout CHILD is borrowed by actual LinuxProcessReplaceOwnerV1,
which validates and retains a private duplicate before yielding. Open returns
bootstrap's original immediately even with an owner; bootstrap retains and closes
that original independently. The original Host source/quota/exclusion are not
transferred. Replacement receives exact signed full argv, explicit private
environment, approved agent digest/exact size/maximum/ISA and original preparation/expiry budget. Its
actual sealed image, sole-thread/signal/fd-table/cwd mechanism is a separate
independently reviewed dependency. Successful exec never returns. A failure keeps
replacement cleanup and its private cwd restoration before bootstrap retirement;
close never returns the original checkout a second time.

The thin main loops actual bounded owner steps without sleeping after each
productive64KiB exec-copy/hash step (no fixed step-count or refreshed deadline). On an owned error it drives
cleanup. If native ownership or cleanup is uncertain, it remains the same
primary with custody until genuine Host workload control/timeout ends it; it
does not convert an unresolved child into a clean exit. After confirmed local
cleanup it exits failed. Host-side dirty/failed retention, charge and exclusion
remain held independently. Bootstrap markers, PID continuity and worktree
verification never report AgentObserved or InteractiveReady; the original native
subject's executable/argv observation and actual smux/Input/Geometry gates are
still required.

Primary command references: [git-worktree](https://git-scm.com/docs/git-worktree),
[git-init](https://git-scm.com/docs/git-init),
[git-fsck](https://git-scm.com/docs/git-fsck), and
[git-config](https://git-scm.com/docs/git-config). These support command semantics,
not an executed fixture or native acceptance claim.

Source unit contracts and actual retained-template fixtures are authored. No
end-to-end qualified Host/Container/agent fixture is claimed here. Compiler,
runtime, native, docgen, real image closure/capability qualification, credential
projection, source authorized cleanup and Windows support remain NOT_RUN or
explicitly incomplete. No release admission follows from this slice.

The required exec/fullV2 rebind is detailed in [agent_workspace_bootstrap_exec_rebind_v2.md](agent_workspace_bootstrap_exec_rebind_v2.md).
Ordinary symlinks and uninitialized gitlinks remain supported; historical
regular-only bootstrapR2 is DO_NOT_LAND. The adjacent ordinary-mode fixture has
real loose assets and a compiled validator, AUTHORED_NOT_RUN; its actual outside
sentinel/Host fixture provisioning driver remains NOT_AUTHORED.
