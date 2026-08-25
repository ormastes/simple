# SimpleOS server external receipt replay

Status: TODO acceptance contract. This manual mirrors
`test/03_system/check/simpleos_server_external_receipt_replay_spec.spl`; it was
not generated in this worktree because no admitted pure-Simple runtime is
available. Regenerate it with `spipe-docgen` before implementation acceptance.

## Admit one immutable three-architecture bundle

1. Authenticate the outer reviewer before loading bundle attachments.
2. Require exactly `x86_64`, `arm64`, and `riscv64`.
3. Replay every signed role from immutable committed evidence.
4. Expect `PASS architectures=x86_64,arm64,riscv64` only after all semantic
   checks succeed.

## Reject malformed or legacy evidence

Reject missing, duplicate, extra, swapped, forged, tampered, and legacy-v1
bundle evidence through the production owner.

## Reject unsafe or aliased identities

Reject noncanonical repository paths and duplicate HEAD path or Git blob
identity before materialization. Post-copy inode checks are defense in depth,
not source-identity proof.

## Replay claimed server behavior

Independently replay retained HTTP file, database commit/reboot/read, shutdown,
and no-host-fallback evidence. Signed boolean fields alone are insufficient.

Fixture or source-contract success never promotes the production TODO row.
