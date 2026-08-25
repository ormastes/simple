<!-- codex-research -->
# Domain research: checked aspect-component admission

Content-addressed artifact systems separate selection metadata from payload
bytes and verify the payload before expensive processing or activation. The OCI
content-descriptor specification is a useful primary reference: descriptors
carry a required media type, digest, and byte size; consumers should verify size
and digest before trusting retrieved content. Simple's existing SMF/aspect-pack
hash and interface gates already align with this model.

As a repo-specific inference, an aspect component descriptor should identify its
artifact kind, path, byte size where available, artifact digest, catalog path,
catalog digest, interface identity, and activation policy. Selection is pure;
filesystem access follows only a dynamic decision. Registration and catalog
publication are transactional so corrupt, stale, mismatched, or denied content
cannot leave partial visible state.

Primary reference:

- [OCI v1.1 content descriptors](https://github.com/opencontainers/image-spec/blob/v1.1.0/descriptor.md): media type, digest, size, and verification-before-use model.
