# SOSIX FAT32 positioned-I/O acceptance manual

## Purpose and audience

This manual is for the owner qualifying the SOSIX syscall 134/135 FAT32 lane.
It mirrors
`test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl`. The executable
spec is authoritative. This Markdown mirror was prepared while no admitted
Stage-4 runtime was available; it must be regenerated with `spipe-docgen` and
reviewed before runtime PASS is claimed.

## Preconditions

- A source-matched, pure-Simple self-hosted Stage-4 runtime.
- A closed runtime receipt accepted by
  `scripts/check/check-sosix-qemu-runtime-admission.shs --verify`.
- A freshly linked, nonzero-entry x86_64 kernel ELF containing strong
  `shim_init`, `spl_handle_fs_pread_registered_v1`, and
  `spl_handle_fs_pwrite_registered_v1` symbols.
- Environment variables `SOSIX_POSITIONED_SIMPLE_RUNTIME`,
  `SOSIX_POSITIONED_RUNTIME_RECEIPT`, and `SOSIX_POSITIONED_KERNEL_ELF`.

The Rust seed, Stage 2/3 bootstrap binaries, stale receipts, and retained
pre-positioned kernel ELFs are inadmissible.

## Operator workflow

1. Set the three qualification variables to canonical files.
2. Run the executable SSpec once with the admitted runtime.
3. Confirm the source/rejection scenario passes.
4. Confirm missing qualification fails before focused tests execute.
5. Confirm linked admission completes before the three focused specs.
6. Retain the runtime SHA-256 and linked artifact provenance beside the run.
7. Run `spipe-docgen` once and replace this pending mirror only if it reports
   complete documentation with zero stubs.

```sh
"$SOSIX_POSITIONED_SIMPLE_RUNTIME" test \
  test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl \
  --mode=interpreter

"$SOSIX_POSITIONED_SIMPLE_RUNTIME" spipe-docgen \
  test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl \
  --output doc/06_spec --no-index
```

## Scenario narratives

### Validate the concrete positioned owner

The source gate requires the explicit FAT32 `read_at`/`write_at` primitives,
generation-safe file-object facade, concrete SOSIX backend, production shim
retention, dup/fork alias hooks, and exit retirement. It also sabotages linked
admission and runtime identity so a non-ELF or Rust-seed-shaped path cannot be
accepted.

### Reject an unqualified positioned environment

An admission attempt with absent runtime, receipt, and kernel paths must return
nonzero and identify runtime admission as the first failure. No focused spec is
executed in this branch.

### Bind the admitted runtime

The wrapper verifies the runtime receipt once, admits the linked kernel once,
then executes each focused owner spec once:

- FAT32 positioned primitives;
- canonical FAT32 file-object lifecycle;
- concrete SOSIX FAT32 backend.

Success retains a nonempty runtime SHA-256 marker. This proves the focused
host-side implementation path, not QEMU guest execution or the 24-row matrix.

## Requirements and scorecard

| Requirement | Scenario coverage | Expected result |
| --- | --- | --- |
| REQ-SQ-018 | concrete owner + qualified suite | true offset I/O, holes, bounds, cursor preservation |
| REQ-SQ-019 | concrete owner + qualified suite | monotonic identities, aliases, retirement, stale rejection |
| REQ-SQ-020 | all three scenarios | authenticated receipt/link admission and fail-closed absence |

Manual-quality target: real assertions in every scenario, zero placeholders,
zero docgen stubs, and all seven `sspec-maintain` component scores reviewed.
Those machine scores are pending the qualified runtime.

## Findings and remediation

- `BLOCKED`: no admitted source-matched Stage-4 runtime currently exists.
- `BLOCKED`: the retained x86_64 kernel predates the positioned shim symbols.
- `NOT CLAIMED`: successful FAT32 syscall execution inside QEMU.

Remediation is one admitted rebuild, linked admission, one SSpec run, one
docgen run, and one `sspec-maintain scan`. Do not substitute the Rust seed or
repeat already-green canonical matrix rows.

## Evidence and provenance

The wrapper emits only these positive markers after their owning gate passes:

- `sosix_fat32_positioned_linked_route=pass`
- `sosix_fat32_positioned_primitives=pass`
- `sosix_fat32_file_object_owner=pass`
- `sosix_fat32_positioned_backend=pass`
- `sosix_fat32_positioned_runtime_sha256=<sha256>`
- `sosix_fat32_positioned_acceptance=pass`

Retain stdout, stderr, runtime receipt, runtime hash, kernel hash, source
revision, and the generated manual together. Source self-test output is only
source-contract evidence.

## Compatibility and limitations

Positioned operations never emulate `seek + read/write + restore`. Sequential
aliases share one canonical cursor; positioned operations preserve it. Buffer
bytes cross the SOSIX boundary as owned copies. Registry installation remains
explicit and fail closed until an authenticated service owner publishes its
capability and registered-buffer state. External Windows, FreeBSD, macOS, and
unverified Linux guest rows retain their existing non-PASS classifications.
