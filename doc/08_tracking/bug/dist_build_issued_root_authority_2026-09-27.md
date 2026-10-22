# Issued distributed-build root lacks an installed authority check

Status: OPEN. Priority: P1. Owner: distributed-build admission lane.

The production issued-graph and issued-staged entrypoints select the fixed
`/etc/simple/dist-build` root, then read a digest-named record. The record
stores verify its bytes and reject a symlink at the final file, but
`issued_store_root_valid_v1` checks path syntax only. They do not establish
that the root, its `graph-plans`/`staged-plans` child, every ancestor, and the
final record are owned by UID 0, non-writable by untrusted users, and opened
without symlink traversal. A writable or replaced component could let a caller
install its own digest-correct record. The fixed path is necessary but does
not alone make the record trusted.

The existing descriptor snapshot facade exposes kind and mode but not owner
UID or a confined directory walk. The cache and hosted-artifact native owners
have no-follow component-walk mechanics, but neither verifies owner UID or
write bits. A path-based `stat` followed by a separate read would leave a
replacement window. Implement one small native descriptor-based authority
primitive through an owned Simple facade: open each component from `/` with
no-follow, verify UID 0 and group/other write bits on each opened descriptor,
then read and verify the final digest-named record through its retained
descriptor. Do not accept the invoking unprivileged UID as an issuer.
Keep policy and record parsing in `.spl`; do not add a broad shell command or
accept a caller-supplied root in the installed entrypoint.

Acceptance: an administrator-owned installed root admits a pinned record;
group/other-writable ancestor, store or final record, wrong owner, symlinked
component, and substituted file cannot authorize execution. A concurrent
pathname replacement must not redirect admission to unauthorized bytes;
reading a previously opened trusted object is valid. Recheck authority on each
launch, bind the opened record bytes to the supplied digest, and run the native
fixture on the installed pure-Simple binary. The current `/etc` root is a Linux
target: macOS `/etc` normally resolves through a symlink, so a separate trusted
canonical Mac root must be selected before a Mac issued-entrypoint claim.
Until this passes, issued entrypoints remain source drafts and must not receive
privileged credentials or state access.
