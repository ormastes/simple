# Simple toolchain signed-catalog media gap

## Status

Open — loader-private preparation and cleanup foundations exist. The 64-bit
media request is deliberately fail-closed because the current hosted-safe
publisher cannot atomically publish three records. Atomic media publication,
atomic triplet ingestion, signer initialization, and a privileged caller remain
required.

## Static audit

- x86_64, ARM64, and RV64 have signed Simplebox SCR1 ingestion, but that record
  covers `/bin/simplebox` and its coreutils aliases only.
- Existing filesystem-exec smoke entries directly read or launch
  `simple_compiler`, `simple_interpreter`, and `simple_loader` payloads without
  proving that those three paths are sealed catalog rows.
- ARM32 mounts the canonical FAT32/VFS owner but has no generated ARM32 trust
  configuration or SCR1 boot-ingestion adapter.
- The image builder recognizes a complete 64-bit signed-toolchain request, but
  rejects it before reading signing material or publishing output. Sequential
  publication could leave one or two durable records after a later failure and
  cannot honestly implement the required all-or-nothing boundary.

## Implemented resume boundary

`simple_toolchain_signed_catalog_boot_v1.spl` is a dormant loader-package
foundation. It requires all three target-bound catalog rows to share one signer
and trust root, and its error paths retire prepared handles/tokens before
restoring the VFS lease. It is not invoked by boot and cannot currently prepare
an admission because the online signer has no production initializer. The
optional availability probe does not affect ordinary boot when records are
missing; no path falls back to resident or cached bytes.

## Remaining unblock conditions

1. Extend the atomic catalog composition owner with a three-record toolchain
   input. Do not ingest the records sequentially: the owner seals the catalog
   once and must authenticate the complete triplet before opening it.
2. Generate and embed x86/ARM32/RV32 trust configurations and catalog-ingestion
   adapters, or explicitly leave those 32-bit targets unavailable in the
   signed-media matrix.
3. Install the loader authority registry and online re-attestation owner from
   boot-owned configuration/secret handoffs,
   with verified seed wiping and the same signer/trust identity as the triplet.
4. Select a real mounted FAT32/DBFS/NVFS source and output path, then invoke
   `simple_toolchain_signed_catalog_boot_launch_v1` with the actual nonzero
   parent task ID before user services begin.

Owner: SimpleOS installer/loader integration. Final reviewer: loader security.

## Wave 17 media boundary

The builder's signed-toolchain request is fail-closed. The current single-file
publisher performs the durable write during prepare and exposes no transaction
or rollback, so the builder does not read the seed or publish any member of the
triplet. A future batch owner must retain one safe-root authority, bind every
identity receipt to the exact staged Simple bytes, pin all three role/target/path
tuples, reject every input/output path collision, verify one shared trust
identity, and only then commit the complete triplet below `/boot/catalog`.

Boot invocation intentionally stays dormant until the catalog composer can
populate all three records atomically and boot supplies both a preconfigured
authority registry and a real nonzero parent task. Missing media remains
optional for ordinary boot; authenticated execution has no resident fallback.

## Wave 18 atomic publication boundary

The current hosted transaction registry intentionally supports exactly one
payload and one SCR1 staged into a private directory followed by one atomic
rename. It cannot safely publish the three toolchain records as one unit, and
the image builder therefore continues to reject signed-toolchain production
instead of performing sequential durable writes.

`simple_toolchain_signed_catalog_batch_v1.spl` now provides the package-private
consumer for the future bounded registry extension. Before any publication it
requires exactly three canonical SAM1 projections and SCR1 envelopes, hashes
the actual shared artifact bytes once, binds every record to the selected
64-bit target and exact interpreter/compiler/loader path, requires one signer
and trust-root digest, and verifies every Ed25519 signature over the canonical
manifest signing domain. The resulting batch carries no publication or boot
authority, so it creates no false reachability while the atomic owner is absent.

## Wave 19 atomic owner

The retained-root transaction now has bounded additive staging for exact source
copies and immutable byte leaves. The toolchain producer streams and hashes the
source once into a private directory, pins its descriptor identity, creates and
authenticates all three canonical SCR1 records, stages three payloads, three
SAM1 projections, three SCR1 envelopes, and one shared trust configuration,
then syncs every leaf and publishes the directory with the transaction owner's
single no-replace rename. Any failure consumes and removes the private tree.

The boot composer accepts the authenticated triplet as one policy input and
adds all three rows before the catalog's sole seal operation. The ingestion
entry remains package-private; ordinary boot does not require this optional
media and the authenticated launch bridge remains dormant until boot supplies
the real authority registry and parent task context.
