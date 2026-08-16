# Feature Expert: SOSIX QEMU Filesystem Matrix

## Source of truth

- Plan: [`sosix_parallel_qemu_refactor.md`](../../../03_plan/agent_tasks/sosix_parallel_qemu_refactor.md)
- Evidence ledger: [`sosix_qemu_matrix_evidence_status_2026-08-13.md`](../../../03_plan/sys_test/sosix_qemu_matrix_evidence_status_2026-08-13.md)
- Operator guide: [`sosix_qemu_shared_settings.md`](../../../07_guide/platform/simpleos/sosix_qemu_shared_settings.md)
- Open owners: [`sosix_qemu_matrix_remaining_owners_2026-08-14.md`](../../../08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md)

## Contract

The matrix is four hosts by six guests. Every row has a stable
`SOSIX-<HOST>-<GUEST>` acceptance ID. A PASS requires admitted native-host
identity, immutable base media plus a row-owned nonce copy, ordered guest entry,
real `/SYS/APPS` listing, mounted program stdout, exit 37, exact reap, and a
producer-generated bundle. The parent collector alone may promote exactly 24
rows. Blocked/postponed rows stay active and are never exclusions or PASS.

The manual flow and shared script names are frozen in the plan. Producer
`--self-test` proves fixture closure only. Windows preflight, TCG correctness,
cached transcripts, and host-side execution are not row evidence. The Windows
peer has six distinct bounded collector-nonce readers. Only x86_64 and ARM32
currently have the complete workload/listing/program/reap source contract;
the other four descriptors must fail before ready. Source gates are not
execution evidence; only native Windows execution can create row evidence.

The L0 collector/media/runtime repairs are implemented in source. Do not call
L0 verified until the bounded typed SSpec passes on a source-matched admitted
full CLI and `spipe-docgen` produces a zero-stub manual. The SSpec's expected
3 PASS / 15 BLOCKED / 6 POSTPONED oracle proves honest handoff state, not live
matrix completion.

The L10 positioned-I/O source lane now owns true FAT32 `read_at`/`write_at`,
generation-safe canonical file objects, dup/fork aliasing, last-alias/task-exit
retirement, and the concrete `SosixFat32PositionedVfsBackendV1` retained by the
production x86_64 shim. Registry installation remains explicit and fail closed;
this is deliberate authority separation, not permission to bypass capability
or owned-buffer authentication.

Qualified acceptance is exactly:

```sh
sh scripts/check/check-sosix-fat32-positioned-io.shs --admit \
  "$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
  "$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
  "$SOSIX_POSITIONED_KERNEL_ELF"
```

The wrapper admits the runtime and linked kernel before executing each focused
spec once. Follow it with the mirrored system SSpec/docgen pair. Never use the
Rust seed, Stage 2/3, source self-test output, or an older linked ELF as
positioned runtime evidence.

Collector v2 now byte-binds the exact 13-field admission record in the
manifest, and the pure-Simple trusted importer exposes only the closed-root
all-24-PASS release predicate. Its multiline boolean forms use the required
parenthesized Simple grammar. Both focused specs and a module check were
attempted once with the deployed self-hosted CLI but exited 139 before usable
results, so they remain unverified without an admitted Stage-4 CLI. Pre/post path/hash checks do not claim
fd-pinned protection against hostile concurrent replacement.

## Update rule

Refresh this expert, the plan, ledger, and guide together whenever a row state,
shared interface, resume command, ownership boundary, or promotion rule changes.

## NVFS/DBFS positioned extension

REQ-SQ-021..023 preserve `MountTable` as the only positioned object owner.
Its virtual handle binds mount, driver family, and opaque driver handle;
SOSIX must call the global VFS positioned facade through
`SosixNvfsPositionedVfsBackendV1` or
`SosixDbfsPositionedVfsBackendV1`. Never expose raw NVFS/DBFS handles as SOSIX
object IDs and never emulate positioned I/O with seek/restore.

The live SimpleOS provider name is exactly `nvfs-dbfs-backed-v1`. That name is
an honesty boundary: NVFS metadata is backed by DBFS on the device. First use
the same qualified runtime to build the dedicated entry, closed kernel
receipt, image, and image manifest:

```sh
SIMPLE_RUNTIME_PATH="$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
SIMPLE_STAGE4_PROVENANCE="$SOSIX_POSITIONED_STAGE4_PROVENANCE" \
SIMPLE_RUNTIME_RECEIPT="$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
sh scripts/check/build-simpleos-nvfs-positioned-qemu.shs
```

Qualified acceptance is then:

```sh
sh scripts/check/check-sosix-positioned-filesystem-matrix.shs --admit \
  "$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
  "$SOSIX_POSITIONED_STAGE4_PROVENANCE" \
  "$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
  "$SOSIX_POSITIONED_KERNEL_ELF" \
  "$SIMPLEOS_NVFS_ROOT_IMAGE" \
  "$SIMPLEOS_NVFS_ROOT_IMAGE_MANIFEST"
```

The gate runs each focused owner spec once and boots a private image copy
twice. Accept only exact mount, cursor-independent round-trip, persistence,
closed kernel/image receipts, and both transcript hashes. The seven-step SSpec manual is future-executable
and unrun while no admitted pure-Simple Stage-4 runtime exists. Source tests,
the Rust seed, Stage 2/3, a handwritten manual, or a single boot are never live
PASS evidence and do not alter the 24-row ledger.
