# SOSIX shared QEMU settings

All SOSIX QEMU lanes use the same host-side settings, admission, media, and
evidence owners. Do not create per-architecture copies of these policies.

## Storage and settings

`scripts/qemu/simple-big-storage-root.shs` resolves the mutable-artifact root
in this order:

1. `SIMPLE_BIG_STORAGE_ROOT`;
2. the workspace-local `.simple-big-storage-root` file; then
3. `$HOME/.simple`.

The root must be absolute. `--prepare` creates the shared bootstrap, QEMU
image, overlay, artifact, and cache directories. Base images remain immutable;
each run creates its own image/nonce derivative below the resolved QEMU root.

Use `scripts/qemu/simple-qemu-settings.shs` as the sole mapping from host and
guest architecture to QEMU binary, accelerator, and storage paths. It supports
`--print`, `--prepare`, `--check`, and `--self-test`. `SIMPLE_QEMU_BIN_DIR`
overrides the QEMU directory and `SIMPLE_QEMU_ACCELERATOR` may select only a
host-valid accelerator. The normal choices are KVM or TCG on Linux, WHPX or
TCG on Windows, HVF or TCG on macOS, and NVMM or TCG on FreeBSD. TCG proves
correctness but never native timing.

## Admission and execution

Before a row starts, invoke:

```sh
sh scripts/qemu/simple-qemu-host-admission.shs --host <actual-host> --arch <guest>
```

It refuses a requested host that differs from the detected host, and records
the resolved QEMU path, SHA-256, version, accelerator advertisement, and a
bounded QMP probe. A Linux run may not be relabelled as Windows, macOS, or
FreeBSD.

`scripts/check/check-sosix-qemu-matrix.shs` owns matrix execution. Every row
gets a separate mutable owner, image copy, collector nonce, and workload nonce.
The collector nonce is a distinct, exactly-once transcript marker; a workload
nonce echoed by both kernel and filesystem program is not collector evidence.

The canonical operator sequence is frozen in
[`sosix_parallel_qemu_refactor.md`](../../../03_plan/agent_tasks/sosix_parallel_qemu_refactor.md):

1. `Validate shared settings`.
2. `Admit the native host row`.
3. `Prepare isolated nonce media`.
4. `Run mounted filesystem execution`.
5. `Produce the canonical row bundle`.
6. `Collect exactly 24 rows`.

The plan is the row-level handoff authority. It assigns stable
`SOSIX-<HOST>-<GUEST>` acceptance IDs to all 24 combinations and records the
exact next command, expected artifact, execution owner, merge owner, and final
reviewer for every blocked or postponed row. Do not infer matrix completion
from this guide or from a grouped host result.

## Media and evidence

Use `scripts/os/prepare_qemu_nonce_media.shs` to patch copied media and verify
readback. The FreeBSD bootstrap path additionally requires an offline,
checksum-admitted qcow2 through `scripts/qemu/simple-freebsd-media.shs --check`;
it never fetches a floating "Latest" image.

A passing row must show, in order, guest entry, a real filesystem listing,
mounted program stdout, exit 37, exact reap, and `TEST PASSED`. Before running
native rows, validate producer closure with:

```sh
sh scripts/check/produce-sosix-qemu-native-pass-bundle.shs --self-test
```

The self-test emits only a temporary fixture. It is not the command that
produces a real row, host admission, or guest evidence. The matrix runner calls
the same producer without `--self-test` only after the admitted row has real
ordered evidence. The parent-only
`scripts/check/collect-sosix-qemu-evidence.shs` accepts exactly 24 valid row
bundles; all unavailable rows stay visible as blocked or postponed in
the [SOSIX QEMU evidence ledger](../../../03_plan/sys_test/sosix_qemu_matrix_evidence_status_2026-08-13.md).
Collector v2 now writes `admission_record_sha256` beside each canonical
cell-relative admission path. The pure-Simple trusted importer consumes the
complete closed manifest and byte-binds the admission, evidence record, and
retained artifacts; only
`sosix_qemu_collector_root_is_release_admissible` crosses the release boundary.
Its focused Simple sabotage specs still require an admitted Stage-4 CLI.
The shared collector/media/runtime source repairs are implemented and covered
by `scripts/check/check-sosix-qemu-shared-owners.shs --self-test`; their modern
typed 24-row SSpec still requires a source-matched admitted full CLI and a
zero-stub generated manual before L0 verification closes.

## Host status

Linux x86_64, ARM64, and RV32 retain canonical evidence. RV64, x86_32, and
ARM32 now have their named compiler/lifecycle owners in source, but remain
blocked on admitted Stage-4 builds and fresh producer bundles. Before QEMU,
run `--admit KERNEL_ELF` on the x86_32/ARM32 lifecycle checks: these use
`readelf` and `nm` to require the correct 32-bit machine, nonzero entry, and
strong linked entry/TSS-or-vector/token/reap symbols. A source self-test is not
linked-artifact admission. The x86_32 source binds the TSS `esp0` stack to its
authenticated task/generation before each CPL3 handoff; admission therefore
requires both `rt_x86_32_tss_set_esp0` and `rt_x86_32_tss_bind_task`. The
rebuild wrapper intentionally includes `src/os`, `src/lib`, and the parent
`examples/09_embedded/simple_os` tree.
Windows and FreeBSD require actual native hosts; macOS is explicitly postponed until a
Darwin executor is available. No host may be counted as PASS from a simulated
or relabelled run.

The host-independent positioned-I/O slice lives under
`src/os/sosix/{core,fs}`. Syscall 134/135 requests cross an authenticated,
owned-copy provider/registry boundary and its backend contract permits only
true `read_at`/`write_at`; compatibility code must not emulate positioned I/O
with seek/read-or-write/restore. FAT32 now owns explicit-offset primitives,
generation-safe open-file objects, alias/retirement lifecycle hooks, and a
concrete SOSIX backend retained by the x86_64 shim. Boot still requires an
authenticated registry owner before dispatch; missing capabilities, owned
buffer registrations, mounts, or live objects fail closed.

After the next admitted rebuild, run the linked/focused gate once:

```sh
sh scripts/check/check-sosix-fat32-positioned-io.shs --admit \
  "$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
  "$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
  "$SOSIX_POSITIONED_KERNEL_ELF"
```

Then execute and documentize
`test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl` once with that same
runtime. The wrapper verifies the receipt and linked strong symbols before it
runs the three focused specs. Exit 139, missing PASS summaries, a Stage 2/3
binary, the Rust seed, or a handwritten manual cannot become runtime PASS.
This focused admission is not QEMU guest or 24-row matrix evidence.

Hosted display/input integration uses the sibling `src/os/sosix/host` seam.
Surface state binds generation and frame sequence with bounded in-flight work;
input state preserves ordered key/text/button events and coalesces only the
declared adjacent pointer-motion case. Headless, SDL2, Win32, and Cocoa
adapters are source-present and have focused specs, but source/static checks do
not prove native fence completion or platform parity.

The Windows PowerShell peer retains fail-closed `-Preflight`. Every guest has a
distinct bounded `/SOSIXNON.TXT` reader in source; sharing the workload nonce
remains forbidden. Only x86_64 and ARM32 also have the complete ordered
workload/listing/program/exit-37/reap source contract. The other four
descriptors return `guest-run-contract-not-implemented:<guest>` before a ready
receipt. The fail-closed source gate
`sh scripts/check/check-sosix-collector-nonce-readers.shs --self-test` passed
once on 2026-08-16. This is not native evidence: none of these paths has been
parsed or executed on Windows. Complete the four guest contracts, then a native
operator must run `-AllGuests -Run` serially and retain six bundles.
FreeBSD first requires checksum-admitted 14.4 media. macOS TCG rows may prove
correctness but never native timing. All non-PASS acceptance IDs remain active;
this is an implementation handoff, not feature completion.

## NVFS/DBFS positioned acceptance

The current SimpleOS NVFS root provider is explicitly
`nvfs-dbfs-backed-v1`. It uses NVFS metadata over a DBFS backing engine; do not
describe it as an independent native NVFS disk engine. SOSIX-facing NVFS and
DBFS backends use `MountTable` virtual handles through the global VFS
positioned facade. Raw driver handles are not capabilities and must not be
passed to SOSIX.

Build the dedicated kernel, closed kernel receipt, image, and image manifest
with the same qualified runtime:

```sh
SIMPLE_RUNTIME_PATH="$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
SIMPLE_STAGE4_PROVENANCE="$SOSIX_POSITIONED_STAGE4_PROVENANCE" \
SIMPLE_RUNTIME_RECEIPT="$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
sh scripts/check/build-simpleos-nvfs-positioned-qemu.shs
```

Set `SOSIX_POSITIONED_KERNEL_ELF` to the emitted
`build/os/simpleos_x86_64_nvfs_positioned.elf`. The adjacent receipt binds the
dedicated entry, target, kernel hash, admitted compiler/runtime identity, and
source revision. Then execute exactly once:

```sh
sh scripts/check/check-sosix-positioned-filesystem-matrix.shs --admit \
  "$SOSIX_POSITIONED_SIMPLE_RUNTIME" \
  "$SOSIX_POSITIONED_STAGE4_PROVENANCE" \
  "$SOSIX_POSITIONED_RUNTIME_RECEIPT" \
  "$SOSIX_POSITIONED_KERNEL_ELF" \
  "$SIMPLEOS_NVFS_ROOT_IMAGE" \
  "$SIMPLEOS_NVFS_ROOT_IMAGE_MANIFEST"
```

The gate first verifies the source and rejection contracts, then runs the
focused FAT32, DBFS, NVFS, and SOSIX owner specs, makes a private image copy,
and boots that copy twice. PASS requires the exact provider marker, the
cursor-independent read/write marker, the first-boot write marker, the
second-boot persistence match, and retained runtime/kernel/image/QEMU plus
boot1/boot2 transcript hashes.
`--self-test`, missing inputs, Stage 2/3, the Rust seed, one boot, or a manual
Markdown mirror is not live QEMU evidence and cannot promote a matrix row.
