# Preparation rejected unrelated namespace mount roots

Status: source correction authored; changed-source native retry pending.

The first real preparation component fixture compiled successfully and exited77
with ENOTSUP95 while parsing actual host mountinfo. No fixture PASS was emitted.
The host had54 rows, including five legitimate nsfs roots of the form
`mnt:[402653…]`. Namespace-type observation itself succeeded. The initial parser
incorrectly treated every filesystem's root metadata as an absolute path.

The correction preserves bounded/control-free opaque roots for unrelated rows,
while every mountpoint remains canonical absolute. Selected XFS source roots
and every same-device alias candidate must still have canonical absolute roots
before any prefix/overlap reasoning. This does not permit opaque data to qualify
a storage scope or bypass writable-alias rejection. Six focused prevention
assertions distinguish opaque metadata from selected security paths and reject
traversal, empty and control-bearing values.

The exact failed helper snapshot, source hashes, original binary hash and logs
are retained under
`doc/06_spec/02_integration/lib/storage_roots/workspace_executable_preparation_v1_native/attempt1/`.
Positive XFS/keeper preparation, Simple execution and release qualification are
not implied by this parser repair.
