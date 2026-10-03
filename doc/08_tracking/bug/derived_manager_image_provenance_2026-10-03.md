# Derived bootstrap support images retain distinct source provenance

The manager policy changes are not part of the frozen a0904ef product source.
The canonical image preparer correctly rejects treating those different bytes
as the admitted Phase2 source. Rebuilding Phase2 on the combined source would
repeat the complete compiler bootstrap before any policy fixture could run.
The shorter diagnostic route builds only the eight support images with the
admitted Phase2 producer and its exact admitted runtime/provider.

Explicit derived-source snapshot, digest and commit options select a separate
`SIMPLE-DERIVED-MANAGER-IMAGES-1` receipt with `canonical_admission=0`.
The canonical source-equality path remains unchanged. The derived receipt binds
the producer bytes, admitted product snapshot, runtime/tool snapshots, helper
source commit/tree and actual helper source snapshot, and installed image hashes.
Support images are one-binary; product builds remain dynload.

The grouped consumer accepts the derived schema only after producer admission
replay and a byte-for-byte helper source snapshot comparison. Git identity alone
is insufficient. It verifies source provenance once per unchanged image receipt,
then continues checking every installed image hash at each use. The operational
handoff separately replays the complete tracked scripts inventory before dispatch.
Product source authority remains the original admitted authority.

The executable shell regression passed once: valid binding, wrong/missing
producer/product/runtime/tool/helper identities, same-commit source mutation,
and altered snapshot. Native runtime compatibility and actual manager capacity,
image startup and worker lifecycle remain UNRUN. An image receipt alone does
not qualify deployment; the operational qualified handoff stays absent until
those actual tests pass. Different runtime providers require their own admission;
the derived option does not permit silently substituting a new runtime.
