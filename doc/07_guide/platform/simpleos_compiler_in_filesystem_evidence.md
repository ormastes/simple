# SimpleOS compiler-in-filesystem evidence

This guide defines the honest admission boundary for REQ-SQ-008. The
collector owns the claim; a filename in a disk image, a host-side `simple`
binary, or a serial transcript alone is not compiler-in-filesystem evidence.

## Current status

The tracked policy is
`scripts/check/lib/sosix-qemu-compiler-designation-v1.tsv`. It contains one
closed row for each of the 24 host/guest cells, and all current rows are
`false`. Consequently no current SimpleOS matrix cell is allowed to claim
that target-native Simple is present in its filesystem. This is intentional:
the policy must be changed only together with the target-native media payload
and its correlated guest execution evidence.

The Unix producer, Unix collector, and PowerShell producer/matrix read the
same policy. The producer requires four regular, non-empty artifacts
(`compiler-version.txt`, `compiler-hello.txt`, `compiler-aliases.txt`, and
`compiler-manifest.env`) for a `true` row, checks
their hashes before and after snapshotting, and rejects symlink and hard-link
aliases. The collector additionally requires both paths to be declared
artifacts and verifies their retained bytes. It then validates the closed
receipt semantics: row host/guest/nonce, mounted `/usr/bin/simple`, canonical
hello source/output paths, zero exits, target-native markers, nonce-bound
stdout, and exact inclusion of every receipt line in the uniquely
hash-selected transcript. The placement receipt contains the closed canonical
compiler/interpreter/loader and `/SYS/SIMPLETOOL.SDN` path set. It is a target
readback contract retained in the serial transcript; the collector does not
pretend that binding `guest.img` alone proves its interior. `/usr/bin/simple`'s
readback digest is the compiler payload identity, and the one-line manifest
binds payload, image, placement receipt, clean source, and nonce. Recomputing
hashes around forged noncanonical receipt content is therefore rejected.

The PowerShell hard-link check depends on native Windows file-identity support,
and the Windows matrix does not yet emit compiler receipts. Its producer now
mirrors the Unix schema and marker/readback semantics, but no PowerShell or
Windows execution PASS was available on the implementation host. Keep Windows
policy cells `false` until a native Windows run verifies both. Static
PowerShell parity is not that evidence.

## Controlled fixtures

`SOSIX_QEMU_TEST_MODE=1` with an explicit
`--compiler-designation-fixture HOST:GUEST` exists only for contract tests.
The resulting source bundle may contain `status=pass` so the producer schema
can be exercised, but the collector rewrites the imported row to
`status=blocked`, records `compiler_designation_scope=contract-fixture`, and
uses `contract-fixture-is-not-release-admissible` as the resume reason. A
fixture must never be used as a live policy value, and setting the environment
variable without the matching explicit fixture coordinate does not enable a
claim.

## Focused checks

Run the producer and collector contract checks from the repository root:

```sh
sh scripts/check/check-produce-sosix-qemu-native-pass-bundle.shs
sh scripts/check/check-collect-sosix-qemu-evidence.shs
sh scripts/check/check-sosix-qemu-native-pass-powershell-parity.shs
```

The PowerShell check reports `BLOCKED` when `pwsh` is unavailable; that is an
environment limitation, not a PASS. Until a real host executes the target
matrix and the policy designates its cell, compiler-in-filesystem evidence is
diagnostic/contract-only and cannot promote a release row.
