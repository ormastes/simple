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
with seek/read-or-write/restore. The x86_64 trap dispatcher now reaches strong
Simple shim leaves and adopts the returned owner state, but boot initializes an
explicit unavailable backend and no production owner installs a replacement.
The current FAT32 driver has no positioned primitive, so this is a live
fail-closed route rather than successful production I/O. Run
`scripts/check/check-sosix-positioned-live-route.shs --admit KERNEL_ELF` after
the next admitted rebuild. Focused specs require a provenance-admitted Stage-4
CLI; exit 139 is not permission to use Stage 3 or the Rust seed.

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
