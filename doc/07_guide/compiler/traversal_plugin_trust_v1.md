# Traversal plugin trust root V1

External traversal providers use an Ed25519-signed canonical SDN allowlist.
The project request names a provider and its allowlist/signature files. It does
not select the verification key.

The host reads `traversal_plugins.trust_root_ed25519` from the user-level
`simple/config.sdn`, resolved through the platform user-config location. The
key is exactly 32 bytes represented by 64 lowercase hexadecimal characters.
The file is read as a bounded regular file without following symlinks. If the
user configuration or key is absent or invalid, provider admission fails with
`traversal-provider-trust-root-unavailable` or a stable trust-config error.

Project `simple.sdn`, command-line arguments, and plugin metadata cannot
introduce or override this key. User-config location follows the platform's
system-location policy. There is no generated default key and no network trust
lookup. Provision the public key through the host user's trusted configuration
before enabling a provider.

Example:

```sdn
traversal_plugins:
  trust_root_ed25519: "<64 lowercase hex characters>"
```

The signing private key is not stored in this configuration. The host binds
the public-key fingerprint into provider policy identity so changing the
trusted signer invalidates prior provider-specific cache admission.
