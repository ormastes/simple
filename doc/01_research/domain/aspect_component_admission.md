<!-- codex-research -->
# Domain research: checked aspect-component admission

Content-addressed artifact systems separate selection metadata from payload
bytes and verify the payload before expensive processing or activation. The OCI
content-descriptor specification is a useful primary reference: descriptors
carry a required media type, digest, and byte size; consumers should verify size
and digest before trusting retrieved content.

Simple has only a partial starting point for this model: structural and CRC
validation exists, a whole-pack SHA-256 helper exists but is not wired into
registration, and ABI/interface expectations are currently optional. Pack
registration and catalog installation are separate, and startup can retain
earlier registrations after a later failure. Therefore the properties below
are target recommendations rather than descriptions of the current system.

As a repo-specific inference, an aspect component descriptor should identify
its artifact kind, path, byte size where available, expected artifact digest,
catalog path, expected catalog digest, mandatory interface identity, and
activation policy. Selection should remain pure and precede filesystem I/O;
filesystem access should follow only a dynamic decision. Digest and interface
checks should precede activation. Pack registration and catalog publication
should form one atomic transaction so corrupt, stale, mismatched, or denied
content cannot leave partial visible state.

The companion feature and NFR options remain subject to explicit user
selection; this research does not choose an implementation policy.

Primary reference:

- [OCI v1.1 content descriptors](https://github.com/opencontainers/image-spec/blob/v1.1.0/descriptor.md): media type, digest, size, and verification-before-use model.
