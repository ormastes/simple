# Shared SOSIX/QEMU Settings

## Canonical ownership

All SimpleOS system tests consume `src/os/qemu_systest_contract.spl`. It is the public façade for versioned guest descriptors; `src/os/_QemuRunner/` owns execution. `scripts/qemu/simple-qemu-settings.shs` is the reusable host path/storage/accelerator preflight. Do not copy emulator arguments into a spec or feature script.

Each descriptor supplies guest ISA/width, emulator/machine/CPU, firmware, accelerator policy, memory, kernel and filesystem media, serial/QMP/network settings, timeout, required markers, and artifact root. Host overrides may select paths and available accelerators but may not change semantic markers or turn missing prerequisites into PASS.

## Operator flow

1. Run `scripts/qemu/simple-qemu-settings.shs --print` to inspect the resolved host, accelerator, storage paths, and five QEMU binary names used by the six guest rows. Run the same command with `--prepare` to create the isolated storage directories, then with `--check` to validate writable storage and fail closed on any missing binary.
2. Resolve the host capability and guest descriptor.
3. Print and retain the exact argv before launch.
4. Prepare isolated overlay/media; never mutate a shared base image.
5. Boot with a bounded timeout and capture the complete serial stream.
6. In guest, list the mounted filesystem and run an arbitrary program from it.
7. Retain hashes, identities, argv, accelerator, transcript, output, rc, and status/reason.

Current reusable entry points include the per-architecture specs in `test/03_system/os/qemu/`, `scripts/check/qemu-storage-audit.shs`, and the FreeBSD Linux-host wrapper `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`. On Unix hosts, aggregate preflight is `scripts/check/check-sosix-qemu-matrix.shs --all-guests --preflight`; on Windows use `scripts/check/check-sosix-qemu-matrix.ps1 -AllGuests -Preflight`. Bounded execution uses `scripts/check/check-sosix-qemu-matrix.shs --all-guests --run --parallel` (or `-AllGuests -Run -Parallel` on Windows): each Unix spec receives a 900-second outer limit and a 180-second test timeout. Both schedules execute all six rows with isolated logs, wait for every row, write a deterministic aggregate, require complete media, and reject a deployed bootstrap seed.

Prepare directories once with `scripts/qemu/simple-qemu-settings.shs --prepare` (the lower-level equivalent is `scripts/qemu/simple-big-storage-root.shs --prepare`). This host stores its ignored `.simple-big-storage-root` setting as `/mnt/data/.simple`; another host with no override defaults to `$HOME/.simple`. QEMU lanes use the reported `qemu/images`, `qemu/overlays`, `qemu/artifacts`, and `qemu/cache` paths. The bootstrap wrapper also defaults its stages, logs, Rust authority workspace, and reusable native cache to the reported `bootstrap` path. An explicit `bootstrap-from-scratch.sh --output=...` remains authoritative. Changing the setting does not move or delete artifacts from the previous root.

The immutable compiler-authority publication target is configured separately
because it moves generations, locks, the current marker, compatibility view,
seed, native library, and backfill authority as one trust boundary. On a host
whose repository filesystem cannot hold that authority, use an existing
absolute non-symlink directory on big storage:

```bash
SIMPLE_BOOTSTRAP_AUTHORITY_TARGET_ROOT=/mnt/data/.simple/bootstrap-authority/current \
  scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
```

The parent directory must already exist. Relative paths, symlink roots, and
missing parents fail closed. This variable does not change `--output`; omitting
it preserves the repository-local `src/compiler_rust/target` default.

Host overrides are `SIMPLE_QEMU_HOST`, `SIMPLE_QEMU_BIN_DIR`, and `SIMPLE_QEMU_ACCELERATOR`. They are explicit configuration inputs, not permission to relabel a host. `scripts/qemu/simple-qemu-host-admission.shs` compares the requested host with the actual OS and proves both accelerator advertisement and a bounded QMP execution before a Unix row is admitted. The Windows wrapper independently rejects non-Windows execution before creating evidence. Unsupported or unproven host/accelerator pairs fail closed. Run `sh scripts/check/check-simple-qemu-settings.shs` and `sh scripts/check/check-simple-qemu-host-admission.shs` after editing resolution logic.

Cross-host results are transferred as the closed-schema bundles documented by `scripts/check/collect-sosix-qemu-evidence.shs --schema`. Import them with `--source-root`; the collector requires exactly 24 unique host/guest cells, rejects relabeling and stale hashes, and writes a content-addressed immutable matrix under the configured large-artifact root.

Every `status=pass` row, including all six Linux guest rows, is also admitted through the shared lineage gate. Its `source_identity` must be `git:COMMIT:tree:TREE:clean` with a real SHA-1 or SHA-256 object-id width. Its 16–128 character `run_nonce` must occur literally in the one artifact selected by `transcript_identity=sha256:HEX`. A dirty/ambiguous source claim, malformed nonce, missing transcript, duplicate transcript hash, or stale transcript is rejected. Blocked and unsupported rows are exempt because they honestly claim that no correlated guest run occurred; they remain subject to the collector's owner, reviewer, reason, resume-command, and artifact checks.

The current-schema macOS postponement receipts are retained under `/mnt/data/.simple/qemu/artifacts/sosix-qemu/native-bundles-v3/macos/<guest>/`. They are six explicit `blocked` rows, not execution evidence, and must be replaced, not edited into PASS, after native admission and execution. The retained v3 receipts contain the older serial resume string; the current operator command is `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --all-guests --run --parallel`. Refresh blocked receipts before a new import when native execution is still postponed.

The same root contains generated Windows and FreeBSD non-PASS bundles. Produce
or refresh them with
`scripts/check/prepare-sosix-qemu-external-blocked-bundles.shs --host HOST --output ROOT`.
The command deliberately exits 2 after retaining six `blocked` rows, records
the actual host and FreeBSD media status, and refuses a missing-host blocker
when the requested native host is available. These receipts make absence
auditable; they never substitute for the native matrix run.

For the frozen parallel schedule, the authoritative Windows resume is
`powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -AllGuests -Run -Parallel`; the authoritative FreeBSD resume is
`sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --all-guests --run --parallel` on the actual FreeBSD host after the checksum-pinned media and bootstrap smoke gates. Older retained blockers with serial resume strings remain immutable absence evidence, not the current runbook.

Accelerator selection is per guest row. On Linux, `kvm` is retained only for a
guest compatible with the native host ISA (including the corresponding 32-bit
guest on a 64-bit host); cross-ISA ARM, RISC-V, or x86 rows are explicitly
lowered to `tcg`. Admission probes and run workers consume that exact row value,
and each receipt records the row accelerator plus whether native timing applies.
On Windows, the same rule lowers non-x86 rows from `whpx` to `tcg`.

`SIMPLE_BIG_STORAGE_CONFIG` may point at an alternate one-line local-config
file for isolated agents and tests. It changes where the workspace-local value
is read, not the precedence: `SIMPLE_BIG_STORAGE_ROOT` still wins, followed by
that config file, then `$HOME/.simple`. The contract test exercises both
environment and config precedence without modifying this workspace's
`.simple-big-storage-root`.

For an implementation vertical slice, select exactly one guest without
weakening the release matrix:

```bash
sh scripts/check/check-sosix-qemu-matrix.shs --guest x86_64 --preflight
sh scripts/check/check-sosix-qemu-matrix.shs --guest x86_64 --run
```

Valid selectors are `x86_32`, `x86_64`, `arm32`, `arm64`, `riscv32`, and
`riscv64`. `--guest` and `--all-guests` are mutually exclusive. Release
verification always uses `--all-guests`; a passing vertical slice cannot close
the other rows.

Every guest row first runs the shared architecture-envelope gate:

```bash
sh scripts/check/check-simpleos-fs-exec-kernel-elf.shs GUEST KERNEL_ELF
```

It checks the guest-specific ELF class and machine, little-endian executable
type, nonzero entry, loadable segments, absence of PT_INTERP, and absence of
strong undefined symbols. The five currently retained non-ARM64 kernels pass
this gate. ARM64 additionally runs its stronger runtime-symbol gate:

```bash
sh scripts/check/check-simpleos-arm64-fs-exec-elf.shs \
  build/os/simpleos_arm64_fs_exec.elf
```

It requires an ELF64 little-endian AArch64 executable with loadable segments,
no interpreter, no strong undefined symbols, and strong (not weak) definitions
of `rt_array_copy` and `rt_enum_id`. Matrix preflight invokes it automatically
after confirming that the ARM64 kernel and image exist.

Cross-host aggregation uses
`src/os/sosix/qemu_evidence/matrix_contract.spl`. A complete manifest has
exactly 24 unique cells: four hosts times six guests. PASS requires an evidence
path. Failed, blocked, and unsupported rows require a reason, artifact path,
resume command, owner, and reviewer. Any missing/duplicate cell or malformed
row fails the aggregate; any well-formed non-PASS cell keeps it blocked or
failed.

## Evidence truth

- TCG is correctness evidence only.
- KVM, HVF, or WHPX credit requires availability plus the exact executed argv.
- Missing host, firmware, media, binary, marker, listing, or program receipt is blocked/failed, never skipped.
- Every evidence row records both `firmware_identity` and `firmware_mode`. An
  empty or absent field is malformed evidence. Values such as `none:*`,
  `implicit:*`, and `unrecorded` honestly preserve a diagnostic row but do not
  prove board-representative firmware.
- macOS postponement requires an open resume record with exact command and artifact location.
- A host `ls`, host compiler, fixed response, or Rust-seed substitution cannot satisfy guest filesystem execution.

## Guest filesystem proof

Every row captures a boot marker, mount identity, in-guest directory listing, expected payload name, program command, stdout, and rc=0. Compiler-in-filesystem claims additionally require the target-native payload paths listed by the SPipe skill, `/usr/bin/simple --version`, and compilation/execution of a small `hello.spl` from the mounted filesystem.
