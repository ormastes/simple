# Generic external receipt semantic quarantine

## Status

Open. The must-check registry has 19 external-receipt rows. Four currently
replay gate-specific evidence (`riscv32-riscv64-shared`,
`binary-size-go-parity`, `interpreter-startup-parity`, and
`rust-go-benchmark-parity`); the other 15 authenticate reviewer signatures and
generic PASS labels without independently replaying the claimed semantics.

## Containment

All 15 generic production rows now fail closed after signature authentication
and before loading generic attachments: the five Caret rows plus
`web-server-request-port`, `web-server-gpu-nginx`, `db-server-request-port`,
`db-server-gpu-sql`, `simpleos-sbc-qemu-ls`, and
`simple-generated-vhdl-linux`, together with `windows-hook-installation`,
`simpleos-clang-hello`, `simpleos-simple-toolchain`, and
`simpleos-server-executables`. A private `fixture-generic` row preserves common
framework coverage only when `MUST_CHECK_SELFTEST=1` and the validator runs
against an isolated fixture root.

## Remaining work

Each quarantined row needs a versioned, registry-owned semantic checker before
it can admit evidence. `simpleos-server-executables` is the nearest wiring
candidate: its existing validator already checks signed per-architecture
receipts and retained artifacts, but the external v2 summary does not bind or
invoke those inputs. The Windows checker validates only live host state, the
clang path has no standalone replay schema, and the SimpleOS toolchain guest
workflow remains disabled. Until those contracts are wired, the ledger rows
remain TODO.

### SimpleOS server bundle replay contract

Do not rewrite a signed `SimpleOsServerExecutionReceiptV1`: its seven absolute
paths are producer-time metadata covered by the inner signature. Add a
resolver-based bundle mode to
`scripts/check/check-simpleos-filesystem-servers-qemu.shs` that verifies the
receipt bytes and signature, then maps each signed role/path/hash to a distinct
immutable HEAD blob materialized below the external validator's private work
directory. Replay must never dereference the producer-time absolute path.

The reviewer-signed outer bundle must bind one provisioned trust policy and key
plus exactly one receipt/signature and seven artifacts for each of `x86_64`,
`arm64`, and `riscv64`: source manifest, staged image, producer, executable,
kernel, boot-1 serial, and boot-2 serial. Reject missing, duplicate, extra, or
cross-architecture rows; non-normalized inner paths; unsafe outer paths;
symlinks, gitlinks, nonregular blobs, canonical-path or inode aliases; and any
disagreement among the inner hash, outer hash, and materialized bytes.

The current v1 acceptance list is not admissible for this replay: the signed
receipt proves a combined `/SERVERS.ELF` filesystem launch, HTTP file flow,
database commit/reboot/read, shutdown, no host fallback, and credential
zeroization. It does not independently prove distinct web/database binaries,
listener ownership, request transport, or process-tree no-leak. A future
`simpleos-server-executables/v2` contract must therefore use only honest IDs:
`three-architecture-bind,signed-receipts,immutable-artifact-replay,filesystem-launch,http-file,db-commit-reboot,shutdown,no-host-fallback,credential-zeroization`.

Required mutations include missing/duplicate/extra architecture, swapped
receipt/signature/map, receipt or artifact tampering, forged or unpinned key,
fixture policy, missing/duplicate mapping role, signed-path mismatch, unsafe
inner and outer paths, aliasing, every false semantic field, generic-label-only
admission, and legacy v1 acceptance. Remove this row from quarantine only after
the exact valid three-architecture bundle passes that suite.
