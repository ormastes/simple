# Simplebox externally signed catalog provisioner v1

The provisioner consumes an externally signed record; it never owns signing
keys and never synthesizes signatures. The external record is a bounded SCR1
envelope containing the canonical path and aliases, payload digest, SAM1
identity, detached Ed25519 envelope, expected trust-root digest, and exact SAM1
signing bytes.

The hosted entrypoint retains one no-follow root authority while reading both
the payload and SCR1 file through an atomic read operation that creates no
copyable grant. The bounded SCR1 decoder owns the external fields and binds its
embedded SAM1 bytes to the typed manifest projection supplied by authenticated
boot configuration. It hashes the payload, derives the SAM1 identity from the
canonical manifest codec, reconstructs SCR1, and requires byte-for-byte equality
with the external file. Every acquired-root path attempts close, and a close
failure takes precedence over an input error. This binds the safe-I/O receipt,
paths, payload, target, manifest, signature envelope, and trust-root expectation
before a boot bundle exists.

The output is only a loader boot plan. Loader-owned Ed25519 verification still
precedes the irreversible catalog bootstrap session; this module cannot mint
execution or catalog authority. Limits are 16 MiB for the payload and 256 KiB
for SCR1. The flow is linear in payload plus record size and retains only those
two bounded buffers and the canonical SAM1/SCR1 encodings during provisioning.

Static acceptance cases cover decode/encode canonicality and substitution of
the manifest projection, payload, SCR1 bytes, and SAM1 identity. Runtime
execution was intentionally not performed in this change.
