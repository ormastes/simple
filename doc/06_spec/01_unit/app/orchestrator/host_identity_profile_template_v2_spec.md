# Installer-only profile templates and paired data binding

Source: [host_identity_profile_template_v2_spec.spl](../../../../../test/01_unit/app/orchestrator/host_identity_profile_template_v2_spec.spl).
Manually authored companion; **AUTHORED / NOT_RUN**. No live capability is
fabricated: fixture paths are plain metadata for the production pure helpers,
not evidence that an OS projection owner is Ready or current.

The new installer-only `server-ssh-profile-template`, version 1, requires
`authRef`, `trustRef`, `user`, `sshExecutable`, `hostKeyAlias` and `storeRoot`,
with optional `sshDigest`. Unknown, duplicate, wrongly typed and overlong fields
fail. Both credential-path fields are forbidden, including empty placeholders.
The runtime decoder still accepts complete `server-ssh-profile` documents only.

Eight authored scenarios exercise the production selection/completion/
canonicalization and publication-match helpers:

- First setup derives the existing complete profile from supplied path values;
  its canonical SDN and immutable profile digest round-trip unchanged.
- Caller path fields, unknown secret fields, duplicates, coercion and text
  bounds fail strict decoding.
- Wrong reference schemes, root spelling, digest and source kinds fail.
- Root/reference mismatches fail the same pure gate used before publication.
- Complete legacy profiles retain exact paths and their original digest;
  replacement path values and a different pinned alias fail.
- SSH percent/environment expansion syntax fails literal-path validation.
- A native protected root remains unchanged while the supplied ordinary path
  values appear only in the derived full profile.

Actual paired acquisition, namespace/root/file replacement, Service5 versus
interactive Windows, current-proof loss, native cleanup and protected-loader
handoff require independently admitted provider execution. They remain
**NOT_RUN**. The actual command obtains opaque paired proof before these helpers
and again immediately before publication; successful pure metadata checks do
not grant authority.

See [profile installer cases](host_identity_profile_v1_spec.md) and the
[ordered setup guide](../../../../07_guide/tooling/orchestration_host_identity.md).
