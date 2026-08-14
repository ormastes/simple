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

## Host status

Linux x86_64, ARM64, and RV32 retain canonical evidence. RV64, x86_32, and
ARM32 remain blocked on their named compiler/lifecycle owners. Windows and
FreeBSD require actual native hosts; macOS is explicitly postponed until a
Darwin executor is available. No host may be counted as PASS from a simulated
or relabelled run.

The Windows PowerShell peer currently performs fail-closed admission and
artifact readiness only; `-Preflight` is its honest next command. It must gain
the same native guest-run and producer contract before `-Run` can emit a PASS.
FreeBSD first requires checksum-admitted 14.4 media. macOS TCG rows may prove
correctness but never native timing. All non-PASS acceptance IDs remain active;
this is an implementation handoff, not feature completion.
