# SOSIX positioned filesystem matrix acceptance

Status: **future-executable / runtime unrun**. This is a manual mirror of
`test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl`, retained
until a qualified pure-Simple Stage-4 runtime can execute the spec and replace
this mirror through `spipe-docgen`. It is not generated evidence or PASS.

## Purpose and audience

This procedure is for SimpleOS/SOSIX maintainers qualifying FAT32, NVFS, and
DBFS positioned owners plus the x86_64 `nvfs-dbfs-backed-v1` live guest. It
fails closed when any provenance, runtime, kernel, image, or QEMU prerequisite
is absent.

## Requirements

- REQ-SQ-021: DBFS and NVFS provide exact binary positioned operations with
  overwrite, extension, zero-hole, short-EOF, and persistence behavior.
- REQ-SQ-022: `MountTable` virtual bindings are the sole canonical SOSIX
  positioned object authority; stale, raw, wrong-family, and invalid accesses
  fail closed.
- REQ-SQ-023: SimpleOS boots the honestly labeled
  `nvfs-dbfs-backed-v1` root, proves cursor-independent I/O, and observes the
  first boot's persisted value on a second boot of the same private image.

## Qualified environment

All variables are mandatory:

- `SOSIX_POSITIONED_SIMPLE_RUNTIME`: admitted pure-Simple Stage-4 CLI.
- `SOSIX_POSITIONED_STAGE4_PROVENANCE`: matching Stage-4 provenance record.
- `SOSIX_POSITIONED_RUNTIME_RECEIPT`: exact runtime identity receipt.
- `SOSIX_POSITIONED_KERNEL_ELF`: freshly linked dedicated-entry x86_64
  SimpleOS kernel with a closed adjacent `.build_stamp`.
- `SIMPLEOS_NVFS_ROOT_IMAGE`: immutable admitted source image.
- `SIMPLEOS_NVFS_ROOT_IMAGE_MANIFEST`: adjacent provider/hash/source manifest.

The Rust seed, Stage 2/3, an older linked kernel, a missing variable, source
inspection, and `--self-test` are inadmissible for runtime or live-guest PASS.

Construct the kernel/image inputs with
`scripts/check/build-simpleos-nvfs-positioned-qemu.shs`. The kernel receipt
binds `nvfs_positioned_entry.spl`, `x86_64-unknown-none`, the kernel hash, the
admitted runtime as compiler/runtime, and the current source revision.

## Frozen acceptance steps

1. `Validate positioned filesystem source contracts`
2. `Reject an unqualified live-guest environment`
3. `Bind the admitted pure-Simple runtime`
4. `Exercise NVFS and DBFS positioned owners`
5. `Boot the NVFS-backed SimpleOS guest`
6. `Verify cursor-independent guest I/O`
7. `Retain filesystem matrix evidence`

The executable helpers are `run_positioned_filesystem_gate`,
`run_nvfs_qemu_gate`, `qualified_positioned_environment`,
`expect_positioned_backend_evidence`, and
`expect_nvfs_live_guest_evidence`.

## Scenario: source contract and rejection

Run the source gate and require
`sosix_positioned_filesystem_source_contract=pass`. Then invoke the NVFS QEMU
gate with empty admission inputs and require a nonzero exit plus
`stage4-admission-failed`. An accepted empty environment is a failure.

This scenario traces REQ-SQ-021 and REQ-SQ-022. It proves only source shape and
fail-closed admission, not runtime behavior.

## Scenario: qualified owners and live guest

After binding all six qualified values, execute once:

```sh
sh scripts/check/check-sosix-positioned-filesystem-matrix.shs --admit \
  "$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
  "$SOSIX_POSITIONED_STAGE4_PROVENANCE" \
  "$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
  "$SOSIX_POSITIONED_KERNEL_ELF" \
  "$SIMPLEOS_NVFS_ROOT_IMAGE" \
  "$SIMPLEOS_NVFS_ROOT_IMAGE_MANIFEST"
```

Require zero exit, empty stderr, and all markers:

- `sosix_fat32_positioned_acceptance=pass`
- `sosix_dbfs_positioned_primitives=pass`
- `sosix_nvfs_positioned_primitives=pass`
- `sosix_positioned_mount_object_backends=pass`
- `sosix_positioned_production_composition=pass`
- `simpleos_nvfs_image_builder=pass`
- `simpleos_nvfs_boot_contract=pass`
- `simpleos_nvfs_runtime_sha256=`
- `simpleos_nvfs_kernel_sha256=`
- `simpleos_nvfs_kernel_build_receipt_path=`
- `simpleos_nvfs_kernel_build_receipt_sha256=`
- `simpleos_nvfs_source_revision=`
- `simpleos_nvfs_image_sha256=`
- `simpleos_nvfs_qemu_sha256=`
- `simpleos_nvfs_boot1_transcript_path=` and `simpleos_nvfs_boot1_transcript_sha256=`
- `simpleos_nvfs_boot2_transcript_path=` and `simpleos_nvfs_boot2_transcript_sha256=`
- `simpleos_nvfs_positioned_live_guest=pass`
- `sosix_positioned_filesystem_matrix_acceptance=pass`

The QEMU owner must use a private copy, require
`[NVFS] mounted as root filesystem provider=nvfs-dbfs-backed-v1`, observe the
cursor-independent round trip, and retain matching persistence markers across
two boots. One boot is insufficient. This scenario traces REQ-SQ-021,
REQ-SQ-022, and REQ-SQ-023.

## Executable SSpec and doc generation

With the same admitted runtime, execute each command at most once:

```sh
"$SOSIX_POSITIONED_SIMPLE_RUNTIME" test \
  test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl \
  --mode=interpreter

"$SOSIX_POSITIONED_SIMPLE_RUNTIME" spipe-docgen \
  test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl \
  --output doc/06_spec --no-index
```

Run `sspec-maintain scan` once after successful docgen. Missing qualification,
nonzero exit, timeout, missing assertion summary, absent marker, or docgen
stub is BLOCKED/FAIL. Do not retry an unchanged failure beyond the lane's
three-cycle cap.

## Current evidence boundary

Implementation and fail-closed tests are present, but no source-matched
admitted pure-Simple Stage-4 runtime is available in this session. Therefore
the qualified SSpec, docgen, maintenance scan, and live QEMU run are unrun.
This manual records the exact future procedure and makes no runtime PASS,
SimpleOS row promotion, or 24-row matrix-complete claim.
