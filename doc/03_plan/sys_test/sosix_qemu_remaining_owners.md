# SOSIX QEMU remaining-owner system-test plan

Executable spec:
`test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl`.

Focused positioned-I/O spec:
`test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl`, mirrored at
`doc/06_spec/03_system/os/qemu/sosix_fat32_positioned_io_spec.md`.

NVFS/DBFS positioned matrix spec:
`test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl`, manually
mirrored pending qualified docgen at
`doc/06_spec/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.md`.

## Oracle

The spec uses bounded process capture and typed `CommandEvidence` and
`RowOracle` values. The retained handoff oracle contains exactly 24 stable IDs
and expects 3 `PASS`, 15 `BLOCKED`, and 6 `POSTPONED`. The three Linux
lifecycle sources now also have direct-QEMU implementation receipts, but remain
non-PASS here until the self-hosted SSpec/docgen and canonical producer bundles
run. A non-PASS expected state proves
only honest retention in this handoff test; it cannot promote a live row.

## Frozen displayed steps

1. `Validate matrix promotion`
2. `Reject mutable source aliasing`
3. `Bind the admitted runtime`
4. `Admit the Linux guest lifecycle`
5. `Record unavailable native hosts`
6. `Retain the implementation handoff`

## Exact verification commands

After a source-matched admitted full CLI exists, run once:

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl --mode=interpreter
release/x86_64-unknown-linux-gnu/simple spipe-docgen test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl --output doc/06_spec --no-index
```

The test must pass and docgen must report zero stubs. Exit 139, timeout,
missing output, or a handwritten manual is FAIL/BLOCKED, never substitute
evidence.

For REQ-SQ-018 through REQ-SQ-020, first run exactly once:

```sh
sh scripts/check/check-sosix-fat32-positioned-io.shs --admit \
  "$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
  "$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
  "$SOSIX_POSITIONED_KERNEL_ELF"

"$SOSIX_POSITIONED_SIMPLE_RUNTIME" test \
  test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl \
  --mode=interpreter

"$SOSIX_POSITIONED_SIMPLE_RUNTIME" spipe-docgen \
  test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl \
  --output doc/06_spec --no-index
```

The wrapper admits the receipt-bound runtime and linked kernel before it runs
the three focused specs once. `sspec-maintain scan` is also required once after
docgen. Missing qualification is an expected fail-closed result, not a skip.

## Positioned-I/O traceability

| Requirement | Implementation | Focused evidence | System scenario |
| --- | --- | --- | --- |
| REQ-SQ-018 | `fat32.spl` explicit-offset primitives | `fat32_positioned_io_spec.spl` | qualified owner suite |
| REQ-SQ-019 | `fat32_fd_table.spl` object/alias lifecycle | `fat32_fd_table_spec.spl` | qualified owner suite |
| REQ-SQ-020 | concrete backend, shim, lifecycle hooks | backend spec + linked gate | source rejection + qualified admission |
| REQ-SQ-021 | DBFS/NVFS exact binary positioned primitives | DBFS + NVFS integration specs | exercise positioned owners |
| REQ-SQ-022 | `MountTable` virtual binding and concrete SOSIX adapters | positioned backend unit spec | source rejection + qualified owner suite |
| REQ-SQ-023 | `nvfs-dbfs-backed-v1` image, root mount, two-boot persistence | image/boot source specs + live QEMU gate | qualified NVFS live guest |

Manual visibility keeps the three system scenarios visible and folds the
executable source. Evidence is `exec`/`binary`/`log`; no screenshots apply.

## Current implementation evidence

- RV64: Sv39-isolated U-mode, checked ELF/FAT admission, exact fault provenance,
  supervisor-state restoration, generation-bound exact-once reap, and live
  `TEST PASSED` are implemented and directly exercised.
- x86_32: PAE/NX-isolated CPL3, checked ELF/FAT admission, context round trip,
  exact #GP/#PF ownership, generation-bound reap, and live `TEST PASSED` are
  implemented and directly exercised.
- ARM32: EL0 page isolation/W^X, checked ELF/FAT admission, authenticated fault
  and SVC ownership, scrubbed first-entry registers, exact reap, and live
  `TEST PASSED` are implemented and directly exercised.

These receipts close the source/lifecycle implementation blockers in AC-4
through AC-6. They do not promote a matrix row without a source-matched admitted
runtime, canonical producer bundle, executable SSpec, and generated manual.

The current positioned source continuation completes the FAT32 primitive,
canonical object owner, concrete backend, production shim retention, and
dup/fork/exit lifecycle hooks. The system spec and manual are present but
runtime/docgen/maintenance status remains BLOCKED until the admitted Stage-4
environment exists.

The current bootstrap continuation also completes the typed parser-contract
owner and proves Stage 2 plus its sanity gate. Stage 3 selects the transient
per-file module-surface owner, and its provenance hash and actual launch bind
that selection. This lane constructs compact surfaces before pausing the
transient scope, retains compact function headers through desugaring, and
splits the former 60 KiB interpreter source into three physical parser units.
The final bounded run nevertheless released the same first ten surfaces, then
grew from about 4.4 GiB to 8.7 GiB while processing the next closure source and
before an eleventh release receipt. It was terminated before host OOM. Because
the admitted Stage 2 executes its previously compiled release-only telemetry,
the new parse/build/promote substage receipts cannot become observable until a
Stage 3 artifact exists; the remaining owner is therefore honestly bounded to
the Stage-2 compiler's processing of physical source 11, not yet to one of
those substages. A proposed planner receipt producer was rejected in highest-
capability review because its shell transcript was self-asserted and forgeable;
canonical planner admission therefore remains fail-closed. The three-cycle cap
is exhausted. No Stage 4 CLI was deployed,
so the exact SSpec/docgen commands above remain pending and must not be run
against the known-stale release binary.

## NVFS/DBFS positioned matrix continuation

The modern spec uses the exact seven steps `Validate positioned filesystem
source contracts`, `Reject an unqualified live-guest environment`, `Bind the
admitted pure-Simple runtime`, `Exercise NVFS and DBFS positioned owners`,
`Boot the NVFS-backed SimpleOS guest`, `Verify cursor-independent guest I/O`,
and `Retain filesystem matrix evidence`. Its frozen helper vocabulary is
`run_positioned_filesystem_gate`, `run_nvfs_qemu_gate`,
`qualified_positioned_environment`, `expect_positioned_backend_evidence`, and
`expect_nvfs_live_guest_evidence`.

When all six inputs exist, run this admission once:

```sh
SIMPLE_RUNTIME_PATH="$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
SIMPLE_STAGE4_PROVENANCE="$SOSIX_POSITIONED_STAGE4_PROVENANCE" \
SIMPLE_RUNTIME_RECEIPT="$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
sh scripts/check/build-simpleos-nvfs-positioned-qemu.shs
```

This construction must produce the dedicated-entry kernel, its closed build
receipt, the NVFS image, and the image manifest before admission. Then run:

```sh
sh scripts/check/check-sosix-positioned-filesystem-matrix.shs --admit \
  "$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
  "$SOSIX_POSITIONED_STAGE4_PROVENANCE" \
  "$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
  "$SOSIX_POSITIONED_KERNEL_ELF" \
  "$SIMPLEOS_NVFS_ROOT_IMAGE" \
  "$SIMPLEOS_NVFS_ROOT_IMAGE_MANIFEST"
```

Then run the new SSpec, docgen, and `sspec-maintain scan` once with that same
admitted runtime. The wrapper executes each DBFS, NVFS, and SOSIX focused spec
once, copies the admitted image privately, boots it twice, and requires exact
mount, cursor-independent round-trip, and persistence markers. No qualified
Stage-4 runtime is presently available, so these runtime commands are pending;
the source gate and manual mirror do not claim PASS.
