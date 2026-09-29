# Parallel Agent Plan: SOSIX Refactor and Multi-Host QEMU Proof

## Outcome and constraints

Refactor SOSIX without a flag day, consolidate all QEMU configuration into one descriptor/settings owner, and prove boot + guest filesystem listing + arbitrary filesystem program execution for six SimpleOS ISA rows across the applicable host matrix. Existing dirty files belong to other sessions. Shared choke points have one merge owner.

The umbrella remains incomplete. Linux RV64 now has the named/immediate
inline-assembly transport and real user lifecycle in source, but still needs a
Stage-4-proven rebuild and fresh producer bundle. Linux x86_32 and ARM32 have
user-entry/token/trap owners in source; linked-artifact gates distinguish those
sources from an admissible kernel. The x86_32 source now binds `esp0` to the
authenticated task/generation before each CPL3 handoff, but no admitted rebuild
yet proves the new binding symbols are linked. The retained ARM32 kernel passes
its linked gate, while the retained x86_32 kernel predates the binding and is
rejected. Windows now has a six-row descriptor/admission wrapper. All six
guests have distinct, bounded `/SOSIXNON.TXT` readers, but only x86_64 and
ARM32 currently expose the complete ordered workload/listing/program/reap
source contract. Native PowerShell parsing, execution, and bundles remain
unverified.
FreeBSD requires admitted native media/execution; macOS requires native Darwin
execution.  The modern executable handoff spec is
`test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl`; its generated
manual is blocked because the available self-hosted `spipe-docgen` crashed
with exit 139; the same runtime also crashed with exit 139 when executing the
modern SSpec. No hand-written file may substitute for generated evidence.

## 2026-08-16 full-plan continuation status

The broader SOSIX prerequisite set is restored under the canonical feature
slug: local/domain research, selected feature/NFR requirements, architecture,
detail design, and system-test plan. The first host-independent implementation
slice restores typed operation/capability ownership, completion queues,
wait-set/synchronous notification decisions, asynchronous FS client/transport,
completion pumping, OFD sequencing, and the positioned-I/O dependency closure
under `src/os/sosix/{core,fs}`. It includes syscall 134/135
envelopes, authenticated registry/provider transactions, a true positioned
backend contract, value-threaded request-token progression, and a fail-closed
install/dispatch owner. The live x86_64 C dispatcher now routes 134/135 through
strong Simple ABI leaves whose process-owned state is reset at shim startup and
adopted after every request. The default remains explicitly uninstalled and
unavailable: no production owner installs a backend, and the current FAT32
driver exposes only cursor-based I/O, so no production FAT32 positioned adapter
or successful live positioned syscall is claimed.

The typed host seam is also restored under `src/os/sosix/host`, with bounded
display-surface and input-stream state plus configuration, timer, process,
library, and producer contracts. The headless adapter reuses the canonical
backend in `host_compositor_core`; SDL2, Win32, and Cocoa adapters use the same
host seam. Their unit/integration specs are present. These restorations are
host-independent source work, not native producer or visual evidence.

The x86_32 rebuild profile now includes the parent SimpleOS tree, `src/os`, and
`src/lib`; the lightweight rebuild self-test binds that source closure. Both
32-bit lifecycle admission scripts validate actual ELF class/machine/entry and
strong linked symbols with `readelf`/`nm`, rather than accepting source grep.
The RV64 lane adds a behavioral result-boundary spec for exact nonce stdout,
exit 37, truncation, late writes, and stale-output clearing.

Verification is intentionally incomplete. The direct pure-Simple deployed CLI
exited 139 before the positioned-I/O scenario ran and also exited 139 on a
separate source check; neither unchanged criterion is rerun in this session.
There is no provenance-admitted Stage-4 CLI for the new RV64 spec or rebuilt
guest media. No Rust seed or Stage-3 artifact substitutes. Linux x86_32 still
needs one admitted rebuild that makes `rt_x86_32_tss_set_esp0` strong, followed
by one canonical QEMU run; all external-host rows retain their existing
blocked/postponed state.

A bounded typed-evidence audit found that collector v2 published an
admission-record path without an admission-record SHA-256. The collector now
byte-binds that exact record, and a source-present v2 importer validates the
closed 24-row wire, canonical base64/cells/nonces/trailer, admission and
evidence hashes, cross-bound identities, and canonical retained artifacts.
The importer and structural parser now group every multiline boolean expression
at the documented Simple grammar boundary without changing the 13/31-field
wire. Focused mutation/late-row/artifact sabotage specs are present; both were
attempted once with the deployed self-hosted CLI and exited 139 before scenario
output, and a final module `check` printed its target then exited 139. They have
not run on a provenance-admitted Stage-4 CLI. The filesystem wrappers cannot pin a file
descriptor across each hash/read sequence, so hostile concurrent replacement
remains a documented trust-hardening gap. The status is tracked in
`doc/08_tracking/bug/sosix_qemu_v2_admission_record_hash_binding_2026-08-16.md`.

## Objective

Complete the four-host, six-guest SimpleOS filesystem-execution matrix without
shared mutable-media races or false promotion. Every implemented row must boot,
list real `/SYS/APPS`, run a mounted filesystem program, return exit 37, reap
the exact task, and publish a canonical evidence bundle. macOS is postponed
only until a Darwin executor is available.

## Replacement-lane acceptance status — 2026-08-14

The detached replacement lane recovered the complete linear implementation
series onto current `origin/main`. The following acceptance gates passed once
in the replacement worktree: shared settings self-test, matrix self-test,
native producer self-test, direct-kernel v2 schema, RV64 inline-asm transport
guard, x86_32 and ARM32 fail-closed lifecycle self-tests, numbered-artifact and
direct-runtime-env guards, `doc/06_spec` layout, changed-line stub scan, and
shell syntax.

Final pure-Simple source checks are currently blocked by the deployed
`release/x86_64-unknown-linux-gnu/simple` executable: both `check src/compiler`
and focused interpreter `test` invocations terminate with signal 11 (exit 139).
The admitted Stage 3 bootstrap artifact reports
`simple-bootstrap 1.0.0-beta` but does not implement the full CLI `check`
command, so it is not used as a substitute. This is a verification WARN until
a full admitted pure-Simple CLI can execute the remaining compiler/lib/MCP and
focused specs; the Rust seed is not an acceptable fallback.

## Shared contract — owned by root

The following are immutable shared interfaces. Architecture/host lanes consume
them; they must not fork their own variants.

| Interface | Owner | Rule |
| --- | --- | --- |
| Settings | `scripts/qemu/simple-qemu-settings.shs` | Each worktree resolves its configured storage; `simple-big-storage-root.shs` is supporting resolution only, not a competing interface. |
| Admission | `scripts/qemu/simple-qemu-host-admission.shs` | Produced before QEMU; binds actual host, QEMU binary/hash/version and accelerator. |
| Media | `scripts/os/prepare_qemu_nonce_media.shs` | Base images are immutable; each row receives a copied image with separate collector and workload nonce slots. |
| Producer | `scripts/check/produce-sosix-qemu-native-pass-bundle.shs` | The row owner emits one hash/lineage-bound bundle only after real ordered guest evidence. |
| Collector | `scripts/check/collect-sosix-qemu-evidence.shs` | The sole parent-authoritative commit point accepts exactly 24 valid row bundles. |

The separate status authority is
[`sosix_qemu_matrix_evidence_status_2026-08-13.md`](../sys_test/sosix_qemu_matrix_evidence_status_2026-08-13.md);
it keeps every unavailable row visible but is not a sixth execution interface.

The operator-facing settings, storage, admission, nonce, and evidence contract
is [SOSIX shared QEMU settings](../../07_guide/platform/simpleos/sosix_qemu_shared_settings.md).

Before a native-host run, an operator validates producer closure with:

```sh
sh scripts/check/produce-sosix-qemu-native-pass-bundle.shs --self-test
```

The fixture emits a temporary direct-kernel bundle only; it never substitutes
for host admission, real ordered guest evidence, or the real producer
invocation performed by `check-sosix-qemu-matrix.shs` after a passing row.

## Shared-owner implementation and verification status

The detailed ownership/unblock record is
[`sosix_qemu_matrix_remaining_owners_2026-08-14.md`](../../08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md).
The three L0 fail-closed repairs are implemented in source:

1. The collector publishes a pending promotion status whenever any
   accepted row is `blocked` or `unsupported`; a file-validation PASS cannot be
   confused with 24-row matrix completion.
2. Nonce-media preparation rejects identical resolved source and run-image
   paths before any copy/move operation.
3. Compiler-in-filesystem validation uses the row's admitted runtime
   identity, never a hardcoded `bin/simple` or seed-adjacent substitute.

The focused behavioral gate is
`sh scripts/check/check-sosix-qemu-shared-owners.shs --self-test`. L0 remains
verification-open until that gate and the modern SSpec run on a source-matched,
admitted full CLI and docgen produces a zero-stub manual. This verification
state is not permission to weaken the 24-row contract or claim matrix PASS.

## Parallel lanes

| Lane | Scope / exclusive owner files | Current state | Acceptance evidence | Sidecar | Merge owner | Final reviewer |
| --- | --- | --- | --- | --- | --- | --- |
| L0 shared matrix | settings, admission, producer, collector, typed v2 importer, matrix docs | source implemented and importer grammar repaired; typed specs and docgen blocked on admitted full CLI | self-tests; v2 mutation/late-row/artifact sabotage; one pre-admitted bundle per changed schema; collector reject unless exactly 24 | N/A | root | root/high |
| L1 Linux x86_64 | x86_64 OVMF/GRUB fs-exec entry and boot artifacts | canonical PASS | OVMF→GRUB→guest-entry, real listing, mounted program stdout, exit37/reap/PASS | N/A | root | root/high |
| L2 Linux ARM64 | ARM64 direct-kernel fs-exec entry, nonce reader and EL0 lifecycle | canonical PASS | direct-kernel v2 bundle, exact ordered serial lifecycle | N/A | root | root/high |
| L3 Linux RV32 | RV32 direct-kernel trap lifecycle and nonce media | canonical PASS | direct-kernel v2 bundle, M-mode recovery and exact reap | N/A | root | root/high |
| L4 Linux RV64 | RV64 compiler operand transport, real user lifecycle, and focused result-boundary spec | source implemented; verification blocked | provenance-admitted Stage-4 focused spec, fresh rebuild, then canonical run | N/A | compiler owner | root/high |
| L5 Linux x86_32 | Broad i686 source closure plus task/generation-bound GDT/TSS/`esp0`, authenticated token, `enter_user_first`, trap return, and mounted ELF staging | source corrected; retained ELF predates and lacks strong `rt_x86_32_tss_set_esp0`/`rt_x86_32_tss_bind_task` | admitted rebuild, passing linked-symbol gate, then live iret/int80/exit37 continuation plus exact scheduler reap | N/A | x86_32 kernel owner | root/high |
| L6 Linux ARM32 | Real `enter_user_first.s`, exception-vector/SVC entry, token/result lifecycle, scheduler binding, and mounted ELF staging | source and retained linked ELF admitted; live row blocked | canonical vector/TTBR lifecycle, target listing/program and exact reap | N/A | ARM32 kernel owner | root/high |
| L10 SOSIX positioned I/O | typed operation/capability owner, true FAT32 explicit-offset primitives, generation-safe file objects, concrete backend, syscall 134/135 x86_64 dispatcher and strong Simple shim leaves | host-independent source complete; authenticated registry installation remains explicit; runtime/link/system execution blocked by absent admitted Stage-4 CLI and fresh kernel ELF | run `check-sosix-fat32-positioned-io.shs --admit` once, then the focused system SSpec/docgen/maintenance gates with the same admitted runtime | N/A | root | root/high |
| L7 Windows | six-row PowerShell descriptors/admission, distinct guest collector-nonce readers, execution, and canonical producer delegation | six nonce readers and x86_64/ARM32 full run contracts are source implemented; four rows fail closed on incomplete guest run contracts; no native verification | complete x86_32/ARM64/RV32/RV64 workload/listing/program/reap markers, then actual Windows `-Run`; RV64 also needs admitted OpenSBI identity | N/A | Windows + guest owners | root/high |
| L8 FreeBSD | image/bootstrap and native FreeBSD matrix execution | blocked external host | checksum-pinned image/bootstrap, then all six FreeBSD bundles | N/A | FreeBSD operator | root/high |
| L9 macOS | Darwin QEMU/firmware/native execution | postponed external host | prepared Darwin host, actual admission and six bundles | N/A | macOS operator | root/high |

## Stable 24-row acceptance matrix

`SOSIX-MATRIX-COLLECT-24` is the umbrella acceptance ID: it passes only when
the parent collector validates exactly one canonical PASS bundle for every row
below and no row remains blocked, unsupported, or postponed.

All rows inherit merge owner `/root` and final reviewer `gpt-5.6-sol` at
normal/highest capability. Artifact paths are beneath the immutable shared
root `/mnt/data/.simple/qemu/artifacts/sosix-qemu/`; a target-host operator
owns execution and a row owns only its per-run mutable directory. `PASS` rows
are retained evidence and must not be rerun unchanged.

| Acceptance ID | Status | Prerequisite or authoritative evidence | Exact resume command | Row artifact / expected output | Execution owner |
| --- | --- | --- | --- | --- | --- |
| `SOSIX-LINUX-X86_64` | PASS | `linux/x86_64-ovmf-canonical-20260813-final/canonical-root/linux/x86_64/run-X86_64_COLLECTOR_NONCE_20260813_V3/evidence.env` | N/A — immutable retained PASS | named evidence bundle | Linux x86_64 owner |
| `SOSIX-LINUX-ARM64` | PASS | `linux/arm64-canonical-v21-20260812/canonical-root/linux/arm64/run-arm64-collector-v21-20260812-n1/evidence.env` | N/A — immutable retained PASS | named evidence bundle | Linux ARM64 owner |
| `SOSIX-LINUX-RISCV32` | PASS | `native-v2-1832753b/linux/riscv32/run-COLLECTOR-RV32-1832753B-A/evidence.env` | N/A — immutable retained PASS | named evidence bundle | Linux RV32 owner |
| `SOSIX-LINUX-RISCV64` | BLOCKED | admitted full CLI must lower named/immediate inline-asm operands and produce a fresh kernel/image | `sh scripts/check/check-sosix-qemu-matrix.shs --host linux --guest riscv64 --run` | `linux/riscv64/<run-id>/evidence.env` or typed blocker | compiler + Linux RV64 owner |
| `SOSIX-LINUX-X86_32` | BLOCKED | strong i686 CPL3 entry/GDT/TSS/token/trap/scheduler symbols and mounted ELF staging | `sh scripts/check/check-sosix-qemu-matrix.shs --host linux --guest x86_32 --run` | `linux/x86_32/<run-id>/evidence.env` or typed blocker | x86_32 kernel owner |
| `SOSIX-LINUX-ARM32` | BLOCKED | strong EL0 entry/vector/SVC/token/scheduler symbols and mounted ELF staging | `sh scripts/check/check-sosix-qemu-matrix.shs --host linux --guest arm32 --run` | `linux/arm32/<run-id>/evidence.env` or typed blocker | ARM32 kernel owner |
| `SOSIX-WINDOWS-X86_64` | BLOCKED | producer-backed runner is source-present; native PowerShell/QEMU/media execution is unverified | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest x86_64 -Run` | `windows/x86_64/<run-id>/evidence.env` or typed blocker | Windows operator |
| `SOSIX-WINDOWS-ARM64` | BLOCKED | collector reader is source-present, but workload nonce, listing, and exact program-begin contracts are absent | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest arm64 -Run` | `guest-run-contract-not-implemented:arm64` until guest completion, then canonical bundle | Windows + ARM64 owner |
| `SOSIX-WINDOWS-RISCV32` | BLOCKED | collector reader is source-present, but workload nonce and mounted listing/program/reap contracts are absent | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest riscv32 -Run` | `guest-run-contract-not-implemented:riscv32` until guest completion, then canonical bundle | Windows + RV32 owner |
| `SOSIX-WINDOWS-RISCV64` | BLOCKED | collector/listing/program/reap owners are source-present, but the workload nonce echo and explicit OpenSBI identity/path/version remain required | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest riscv64 -Run` | guest-run blocker, then canonical firmware-bound bundle | Windows + RV64 owner |
| `SOSIX-WINDOWS-X86_32` | BLOCKED | collector/listing/program/reap owners are source-present, but the required workload nonce echo is absent | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest x86_32 -Run` | `guest-run-contract-not-implemented:x86_32` until guest completion, then canonical bundle | Windows + x86_32 owner |
| `SOSIX-WINDOWS-ARM32` | BLOCKED | complete collector/workload/listing/program/reap source contract is present; native execution remains unverified | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest arm32 -Run` | canonical Windows bundle or typed native runtime blocker | Windows + ARM32 owner |
| `SOSIX-FREEBSD-X86_64` | BLOCKED | checksum-admitted FreeBSD 14.4 media and native FreeBSD executor | `sh scripts/qemu/simple-freebsd-media.shs --check && sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --guest x86_64 --run` | `freebsd/x86_64/<run-id>/evidence.env` or typed blocker | FreeBSD operator |
| `SOSIX-FREEBSD-ARM64` | BLOCKED | same FreeBSD media/executor prerequisite | `sh scripts/qemu/simple-freebsd-media.shs --check && sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --guest arm64 --run` | `freebsd/arm64/<run-id>/evidence.env` or typed blocker | FreeBSD operator |
| `SOSIX-FREEBSD-RISCV32` | BLOCKED | same FreeBSD media/executor prerequisite | `sh scripts/qemu/simple-freebsd-media.shs --check && sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --guest riscv32 --run` | `freebsd/riscv32/<run-id>/evidence.env` or typed blocker | FreeBSD operator |
| `SOSIX-FREEBSD-RISCV64` | BLOCKED | same FreeBSD media/executor prerequisite | `sh scripts/qemu/simple-freebsd-media.shs --check && sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --guest riscv64 --run` | `freebsd/riscv64/<run-id>/evidence.env` or typed blocker | FreeBSD operator |
| `SOSIX-FREEBSD-X86_32` | BLOCKED | same FreeBSD media/executor prerequisite | `sh scripts/qemu/simple-freebsd-media.shs --check && sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --guest x86_32 --run` | `freebsd/x86_32/<run-id>/evidence.env` or typed blocker | FreeBSD operator |
| `SOSIX-FREEBSD-ARM32` | BLOCKED | same FreeBSD media/executor prerequisite | `sh scripts/qemu/simple-freebsd-media.shs --check && sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --guest arm32 --run` | `freebsd/arm32/<run-id>/evidence.env` or typed blocker | FreeBSD operator |
| `SOSIX-MACOS-X86_64` | POSTPONED | prepared Darwin executor with native QEMU/firmware/media | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --guest x86_64 --run` | `macos/x86_64/<run-id>/evidence.env` or typed blocker | macOS operator |
| `SOSIX-MACOS-ARM64` | POSTPONED | same Darwin executor prerequisite | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --guest arm64 --run` | `macos/arm64/<run-id>/evidence.env` or typed blocker | macOS operator |
| `SOSIX-MACOS-RISCV32` | POSTPONED | same Darwin executor prerequisite | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --guest riscv32 --run` | `macos/riscv32/<run-id>/evidence.env` or typed blocker | macOS operator |
| `SOSIX-MACOS-RISCV64` | POSTPONED | same Darwin executor prerequisite | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --guest riscv64 --run` | `macos/riscv64/<run-id>/evidence.env` or typed blocker | macOS operator |
| `SOSIX-MACOS-X86_32` | POSTPONED | same Darwin executor prerequisite | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --guest x86_32 --run` | `macos/x86_32/<run-id>/evidence.env` or typed blocker | macOS operator |
| `SOSIX-MACOS-ARM32` | POSTPONED | same Darwin executor prerequisite | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --guest arm32 --run` | `macos/arm32/<run-id>/evidence.env` or typed blocker | macOS operator |

The Windows peer retains `-Preflight` as a readiness-only operator check. Its
x86_64 and ARM32 source-ready `-Run` paths prepare isolated nonce media, execute
QEMU with a bounded serial transcript, validate the ordered lifecycle, and
delegate the PASS bundle to the canonical producer. All six collector readers
are source-present; the other four descriptors stop at
`guest-run-contract-not-implemented:<guest>` before preflight can claim ready.
The fail-closed source criterion
`scripts/check/check-sosix-collector-nonce-readers.shs --self-test` passed once
on 2026-08-16 after its negative-sabotage helper was corrected; it is still not
native execution or row-admission evidence.
Only actual Windows runs can verify these paths; preflight output is never row
PASS. TCG on macOS proves correctness only, not native timing.

## Frozen operator/manual vocabulary

The shared scenario flow uses these phrases exactly, in order:

1. `Validate shared settings` — `simple-qemu-settings.shs`.
2. `Admit the native host row` — `simple-qemu-host-admission.shs`.
3. `Prepare isolated nonce media` — `prepare_qemu_nonce_media.shs`.
4. `Run mounted filesystem execution` — `check-sosix-qemu-matrix.shs`.
5. `Produce the canonical row bundle` — `produce-sosix-qemu-native-pass-bundle.shs`.
6. `Collect exactly 24 rows` — `collect-sosix-qemu-evidence.shs`.

No new helper is introduced by this plan-only lane. A future unresolved setup
or checker helper must fail explicitly with `assert(false)` or `fail(...)`;
silent placeholders cannot satisfy an acceptance ID.

## Parent-authoritative parallel protocol

1. Root freezes the shared scripts and the row descriptor before launching
   child lanes. Each lane gets a unique run ID, artifact directory, nonce pair,
   and no permission to edit shared collector state.
2. Each lane performs only its own source fixes, focused gates, one admitted
   rebuild and one bounded QEMU attempt per fresh diagnostic cycle. It writes
   either a complete producer bundle or a typed blocker receipt.
3. Child lanes return artifact paths, hashes, source commit/tree, first blocker
   and exact resume command. They do not copy a predecessor's PASS into a new
   source lineage.
4. Root verifies source/lineage, calls the producer for a valid row, and invokes
   the collector only with the aggregate source root. Collector rejection is
   expected until all 24 valid bundles exist.

## Dependency order

```text
QemuLaneSettingsV1
QemuHostCapabilityV1
QemuEvidenceBundleV1
SosixOperationId
SosixCompletion<T>
SosixCapabilityRef
SosixBufferRef
SosixFsIpcRequestV1 / SosixFsIpcCompletionV1
```

Canonical descriptor owner remains `src/os/qemu_systest_contract.spl`; implementation may split private modules beneath `src/os/_QemuSystestContract/` while preserving that façade. Existing `QemuRunner` executes descriptors. No lane copies a QEMU argv.

## Evidence matrix

| Host | x86_32 | x86_64 | ARM32 | ARM64 | RV32 | RV64 | Native accelerator |
|---|---|---|---|---|---|---|---|
| Linux | required | required | required | required | required | required | KVM only when host/guest match; otherwise TCG |
| Windows | required | required | required | required | required | required | WHPX only when host/guest match; otherwise TCG |
| macOS | required | required | required | required | required | required | HVF only when host/guest match; otherwise TCG; unavailable rows stay blocked |
| FreeBSD | required | required | required | required | required | required | NVMM/host support only when actually available; otherwise TCG |

Each cell must classify `pass`, `failed`, `blocked`, or `unsupported`. Only a fresh native host receipt can promote that host row. QEMU correctness may be remotely produced; it cannot prove native host runtime support.

The executable aggregation owner is
`src/os/sosix/qemu_evidence/matrix_contract.spl`. It requires exactly one row
for every cell and rejects PASS without evidence or non-PASS without an exact
resume handoff. Host agents return rows to this contract rather than editing a
shared status table by hand.

## Serial preparation — integration owner

1. Freeze settings/evidence schemas and field names.
2. Map existing six descriptors and all wrapper overrides into the schema.
3. Freeze manual steps and artifact convention: `${SIMPLE_BIG_STORAGE_ROOT}/qemu/artifacts/sosix-qemu/<host>/<guest>/<run-id>/`, with resolver fallback to the workspace-local setting and then `$HOME/.simple`.
4. Add fail-fast placeholders for missing lane implementations.
5. Publish the descriptor compatibility test before sidecars edit production files.

## Wave 1 — disjoint refactoring lanes

| WP | Ownership | Work | Acceptance |
|---|---|---|---|
| A SOSIX core | `src/os/sosix/core/**` | typed IDs, completions, cancellation, deadlines, wait-set adapter | unit race/partial-progress/type-confusion tests |
| B SOSIX FS | `src/os/sosix/fs/**` | versioned owned-copy IPC codec, capability `read_at`/`write_at`, completion pump, notification wait, offset/errno-compatible adapters | byte-level codec sabotage, real owned IPC round trip, CPU integration and POSIX parity |
| C QEMU settings | `src/os/_QemuSystestContract/**`, `scripts/qemu/simple-{big-storage-root,qemu-settings}.shs`, setup script additions | descriptor schema, host overrides, storage/host resolver, print/check/prepare | golden argv plus storage precedence, host mapping, and malformed/missing prerequisite failures |
| D Evidence model | `src/os/sosix/qemu_evidence/**` | correlated bundle, hashes, status/reason, accelerator truth | stale/mismatched artifact sabotage fails |
| E Specs | `test/01_unit/os/sosix/**`, `test/02_integration/os/sosix/**` | non-vacuous core/FS/settings tests | real assertions and deliberate red |
| F Docs/wiki | guide, manual, feature/layer expert | operator setup and reusable agent contract | links/commands validated; no behavior claims beyond evidence |
| G Host-service seam | `src/os/sosix/host/**` (new) | display/input/timer/config/file/process/library capability traits and typed async contracts | pure contract/state-machine tests |
| H WM adapter | new adapter files under `src/os/compositor/host_services/**` | migrate configuration, evidence I/O, timing, input, present/readback without changing Draw IR ownership | old-vs-new absolute oracle and no raw host calls in migrated files |

The WP-G pure contract seam is now present at
`src/os/sosix/host/service_contract.spl`. It freezes typed startup
configuration, batched present/readback identities, input-stream generation,
timer deadlines, and stale surface/frame rejection. Adapter implementations
and production-path parity remain open. Its backend-independent surface
lifecycle is `src/os/sosix/host/display_surface_state.spl`: adapter lanes must
use its bounded submission, ordered completion, backpressure, resize-generation
invalidation, and drained-close transitions rather than maintain private frame
ordering state.

The first WP-H adapter is
`src/os/compositor/host_services/headless_display_adapter.spl`. It consumes the
existing real headless pixel buffer and completes through the SOSIX state
machine. The framebuffer backend is now extracted to
`src/os/compositor/headless_host_backend.spl`; the old core façade explicitly
re-exports it while the SOSIX adapter imports the leaf directly. Native adapter
migration must preserve this narrow dependency direction.

Input adapter lanes target `src/os/sosix/host/input_stream_state.spl`. SDL,
winit, USB/HID, PS/2, UART, and virtio producers must publish the same typed
sequence/timestamp contract. They may coalesce only adjacent pointer motion;
key, text, and button backpressure remains observable.

Old `io_state.spl` and `io_rw.spl`, `src/os/qemu_systest_contract.spl`, module exports, and shared scripts are merge-owner only. Lane agents submit integration fragments.

### WM/renderer migration waves

1. Freeze `HostDisplayService`, `HostInputService`, `HostTimerService`, and `HostConfigurationSnapshot`.
2. Snapshot environment/config once during bootstrap.
3. Migrate QEMU/capture file and process operations to async SOSIX operations.
4. Migrate frame deadlines and input delivery to notification-backed operations.
5. Migrate window control, present, and readback with surface-generation/frame-sequence receipts.
6. Remove migrated raw host calls after Linux/headless/QEMU and available native-host parity evidence.

Draw IR, WebIR, WM scene/layout, Engine2D lowering, font batches, and backend GPU resources remain outside SOSIX. A present submits a frame/composition result as one operation; it never decomposes primitives into OS calls.

## Wave 2 — guest lanes

Six independent owners implement or refresh x86_32, x86_64, ARM32, ARM64, RISC-V32, and RISC-V64. Each consumes the canonical descriptor and implements these exact steps:

1. `Load the canonical QEMU settings`.
2. `Prepare isolated guest media`.
3. `Boot the requested host and guest row`.
4. `Inspect the mounted filesystem`.
5. `Run an arbitrary filesystem program`.
6. `Retain the correlated evidence bundle`.

Required transcript facts: boot marker, filesystem mount identity, `ls` output, expected payload path, program argv, program stdout, rc=0, and no fixed-command/stub marker. Compiler payload rows add `/usr/bin/simple --version`, source creation, in-guest compile, and execution.

Current diagnostic `SMF_CLI_LAUNCH_OK`, x86_32 fixed-pid dispatch, and native
GUI marker paths do not meet the arbitrary-program clause: they validate
package/header/marker bytes and construct synthetic process state without
entering the mounted program. REQ-SQ-007 remains missing until a real target
instruction path or defined guest bytecode interpreter emits target-origin
stdout and actual rc. The exact blocker and sabotage contract are recorded in
`doc/08_tracking/bug/sosix_synthetic_filesystem_program_execution_2026-08-12.md`.

## Wave 3 — host lanes

- Linux owner runs all TCG correctness rows and applicable KVM rows.
- Windows owner uses the PowerShell wrapper and returns WHPX/TCG receipts.
- FreeBSD owner first uses `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke` for host preparation, then runs the shared matrix inside the guest/host as designed.
- macOS owner runs Homebrew-QEMU preflight and applicable HVF rows. If unavailable, it retains one collector-schema blocked receipt per guest with the real-host resume command, artifact root, owner, and reviewer; it does not close the row.

## Serial integration and verification

1. Merge shared façades once.
2. Run settings/parser/unit checks.
3. Run one Linux x86_64 boot/list/program vertical slice.
4. Run remaining current-host guest rows once.
5. Collect external-host receipts without relabeling cached evidence.
6. Generate and review the SPipe manual; require zero stubs.
7. Run direct env/runtime guards, lint, duplication, dependencies, focused specs, and release-level tests only at their required tier.
8. Independently sabotage descriptor hash, accelerator classification, boot marker, listing output, and program rc; each must turn red, then revert once.

## Handoff rule

Current-host implementation may finish while external rows remain blocked, but the umbrella feature and verify status remain incomplete. Each blocked cell retains host/capability, prerequisites, exact command, artifacts, owner, and final reviewer.

Current Linux execution is tracked in `doc/08_tracking/bug/sosix_qemu_matrix_media_and_selfhost_blockers_2026-08-11.md`: emulator/KVM readiness is proven, but no guest has a complete fresh kernel+image pair and the deployed CLI is a bootstrap seed. These are active unblock tasks, not exclusions.

## Landed migration seam

The additive typed core now lives under `src/os/sosix/core/`, with filesystem request validation under `src/os/sosix/fs/`. Legacy raw-ID APIs remain compatible, while their live pool begins migrating to generation-checked identity. The next transport wave must store the full `SosixOperationSlot`, wake via notifications, preserve POSIX offset/errno semantics, then delete remaining duplicate/dead owners only after parity evidence.

The first consolidation is now landed: live `io_rw.spl` uses the single `io_state.spl` pool, guarded one-shot finish, typed generation/cancellation bridge, and notification-based compatibility waiting. The unreferenced monolithic `io.spl` remains until an import/dynamic-entry deletion gate proves removal safe. VFS send/receive is still synchronous. Full audit proved syscall 20/21, VFS, SOSIX, and the x86 shim are mutually incompatible, so integration must use a new versioned owned-copy IPC surface rather than reinterpret legacy calls. The correlation state already composes the canonical operation ID with a transport-owned request token; codec, syscall wiring, pump, and POSIX sequencing remain gated in that order.

## Per-run media lineage interface

The shared interface is frozen as `/QEMUNONC.TXT`, 118 bytes, containing
`SIMPLEOS_QEMU_NONCE=<nonce>\n` followed by zero padding. Every row launches a
private cloned image prepared by
`scripts/os/prepare_qemu_nonce_media.shs`; base images remain immutable.
Guest kernels validate the prefix, closed nonce alphabet, bound, newline, and
zero padding before serial emission. The collector accepts only the exact
prefixed marker. Rebuild requirements are all six fs-exec kernels and all six
images; old media intentionally returns `boot-fail:nonce-unsupported`.

## Merge ownership

- Merge owner: SOSIX/QEMU integration owner.
- Sidecars: Spark inventory, Haiku QEMU/docs, Sonnet evidence-matrix audit.
- Final reviewer: normal/highest-capability independent reviewer.

## Authoritative 24-cell completion TODO (2026-08-12 audit)

Evidence source: immutable collector import
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/imported/matrix-v1-3efab06786847296/matrix.env`
(24 rows, all `blocked`). Diagnostic boot/list/program output is retained but
is not a matrix PASS. Row promotion requires a fresh actual-host bundle and a
new content-addressed collector import; this table is a TODO, not a substitute
receipt.

| Host | x86_32 | x86_64 | ARM32 | ARM64 | RV32 | RV64 | Owner / reviewer | Exact resume |
|---|---|---|---|---|---|---|---|---|
| Linux | BLOCKED: diagnostic PASS; seed lineage, dirty source, nonce | BLOCKED: capacity root cause fixed statically (implicit host Simple discovery amplified into 13 FAT chains); fresh admitted image and nonce/list/program run absent | BLOCKED: diagnostic PASS; seed lineage, nonce | BLOCKED: latest diagnostic still ends `executable FAT32 read probe failed` / `TEST FAILED`; fresh admitted build and run absent | BLOCKED: diagnostic PASS; seed lineage, nonce | BLOCKED: diagnostic PASS; seed lineage, nonce | `linux-diagnostic-evidence-owner` / `sosix-qemu-matrix-reviewer` | x86_64 only: `bin/codex exec -C /home/ormastes/dev/pub/simple 'Resume doc/08_tracking/bug/x86_64_nonce_media_payload_capacity_2026-08-12.md; exactly one x86_64 rebuild, then only on success exactly one canonical Linux x86_64 QEMU run with fresh nonce; retain receipts and stop on failure without resize/retry.'`; other rows retain their scoped blocker resumes |
| Windows | BLOCKED: wrapper not run on Windows | BLOCKED: wrapper not run on Windows | BLOCKED: wrapper not run on Windows | BLOCKED: wrapper not run on Windows | BLOCKED: wrapper not run on Windows | BLOCKED: wrapper not run on Windows | `windows-host-operator` / `sosix-qemu-matrix-reviewer` | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -AllGuests -Run -Parallel` |
| macOS | BLOCKED: postponed | BLOCKED: postponed | BLOCKED: postponed | BLOCKED: postponed | BLOCKED: postponed | BLOCKED: postponed | `macos-host-operator` / `sosix-qemu-matrix-reviewer` | `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --all-guests --run --parallel` on an actual macOS host |
| FreeBSD | BLOCKED: host/media | BLOCKED: host/media | BLOCKED: host/media | BLOCKED: host/media | BLOCKED: host/media | BLOCKED: host/media | `freebsd-host-operator` / `sosix-qemu-matrix-reviewer` | obtain checksum-pinned `/mnt/data/.simple/qemu/images/freebsd/FreeBSD-14.4-RELEASE-amd64-BASIC-CLOUDINIT-ufs.qcow2`, run `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`, then `sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --all-guests --run --parallel` on FreeBSD |

Current totals: **PASS 0 / BLOCKED 24**. The Windows PowerShell wrapper exists
and has retained collector-schema blocked bundles, but has no native Windows
execution receipt. The six macOS bundles are deliberate postponements and must
remain visible. FreeBSD is blocked both by absence of an actual FreeBSD host
receipt and by the missing checksum-pinned 14.4 cloud image above.

The retained `native-bundles-v3` blockers predate the parallel-resume freeze and
contain serial resume commands. They remain valid immutable evidence that no
native execution occurred, but they are not the current operator runbook.
Refresh the six blocked bundles with the host-specific owner above before the
next collector import, or replace them directly with native parallel-run
bundles; never edit an existing retained bundle in place.

### 32-bit real-execution ownership update (2026-08-12)

RV32 and x86_32 now share one kernel-only fixed packed-storage owner rather
than passing value-semantic Simple arrays across raw pointer ABIs. RV32 owns
stable 16-byte key and 80-byte SipHash message loans; x86_32 owns a stable
serialized 96-byte privilege token. Exact generation leases, scalar byte
copy, alignment, stale rejection, and volatile wipe are focused PASS. This
closes the former packed-storage prerequisite but not either live trap path.

ARM32 now owns a bounded exact `/FSEXEC.ELF` mounted-byte loan and a dedicated
supervisor continuation endpoint. The endpoint accepts success only after
target stdout equality, user-frame cleanup, exact-generation reap, and exit
37 closure. Source/static and ARMv7 syntax gates pass. A fresh admitted kernel,
nonce-bound media, and one live QEMU execution remain required before changing
the ARM32 matrix cell from BLOCKED.

The canonical ARM32 entry now invokes that lifecycle instead of ending after
synthetic SMF load markers. It initializes the bounded table/frame owners,
installs the frozen vector, stages the exact mounted bytes, publishes one
authenticated token, enters User mode, and can reach final PASS only through
the supervisor closure. The previous unconditional final PASS is absent.

The ARM32 address-space snapshot also now preserves the actual QEMU-virt
identity-mapped kernel range beginning at `0x40000000` (L1 index 1024), rather
than copying only the unrelated upper 2 GiB. The SVC guard is installed before
the child root copies supervisor mappings, so the invalid guard PTE and mapped
exception code/stack are coherent under the user TTBR0. This repair is covered
statically but still requires live exception-entry evidence.

The x86_64 worktree briefly regressed to an unconditional SMF package-probe
PASS. The exact earlier scheduler-owned delta was recovered from its rollout
receipt: TaskId/generation/expected-CR3 token admission, authenticated syscall
60/exit, one-shot result, and exact child reap are restored. Its canonical
entry again performs nonce read, live `/SYS/APPS` listing, and `/FSEXEC.ELF`
handoff. The descriptor now requires target nonce stdout, exit 37, authenticated
reap, and final PASS, while a static sabotage gate rejects the synthetic entry.
Linux/x86_64 remains BLOCKED pending a fresh admitted build and live QEMU proof.

The same concurrent-overwrite audit found the previously implemented RV64
mounted-exec wiring absent. It is restored with the canonical VFS mount, exact
mounted-byte nonce authentication, scheduler user handoff, supervisor-return
reap, and target marker contract. The RISC-V shared and ARM32 live FAT dirent
walkers were also recovered, preventing listing evidence from collapsing back
to fixed package names. Source sabotage and RV64 freestanding C syntax pass;
Linux/RV64 remains BLOCKED until the frozen compiler builds it and QEMU proves
target stdout plus exit/reap.

## SOSIX implementation acceptance TODO (2026-08-12 audit)

These verdicts are independent of the QEMU matrix. `PASS` means the named
focused contract has retained executable/static evidence; it does not promote
REQ-SQ-002/010/014/015 as a whole. `RED` names the missing production
connection.

| Slice | Proven PASS | Current RED | Focused resume command |
|---|---|---|---|
| Async FS | Typed operation/completion FIFO, notification wait state, registered-buffer client plan, nonblocking completion receive, and façade exports exist; scoped conflict/placeholder/direct-runtime gates passed. | No live VFS client/service path owns syscall 132/133 submission through backend completion; the full async round trip is not executable acceptance evidence. | `SIMPLE_LIB=src bin/simple test test/01_unit/os/sosix/fs_async_client_v1_spec.spl --mode=interpreter && SIMPLE_LIB=src bin/simple test test/01_unit/os/sosix/fs_completion_receive_transport_spec.spl --mode=interpreter` |
| IPC v1 | Packed 88-byte request and bounded 48-byte completion contract plus sabotage coverage are implemented. | Executable codec evidence is RED at the pre-existing `src/os/sosix/fs/ipc_codec_v1.spl` parser failure; no authenticated live IPC transport round trip is proven. | `SIMPLE_LIB=src bin/simple test test/01_unit/os/sosix/fs_ipc_codec_v1_spec.spl --mode=interpreter && SIMPLE_LIB=src bin/simple test test/01_unit/os/sosix/fs_service_dispatch_transaction_v1_spec.spl --mode=interpreter` |
| Positioned I/O | OFD sequencer, true-positioned backend contract, FAT32 `read_at`/`write_at`, authenticated provider model, value-threaded dispatch owner, architecture-neutral explicit install/dispatch state for syscall IDs 134/135, and fail-closed libc sabotage exist. Nonempty generic libc `pread`/`pwrite` correctly returns ENOTSUP instead of seek/read-or-write/restore. The dispatch owner is now the sole registry/token transition policy; the kernel wrapper publishes `dispatched.owner` directly. | Earlier scoped evidence was RED at 2/4: registry bytes persisted while the returned nested owner retained token `11` rather than `12`. After policy deduplication, three bounded attempts using the deployed CLI/bootstrap seed timed out during compiler/test-runner startup before any scenario output, so the change is intentionally unverified and the defect remains unclassified between documented interpreter nested-aggregate behavior and SOSIX logic. The kernel seam is not installed by a production trap-runtime lifecycle owner and must remain unwired. | Deploy a usable pure-Simple full CLI, then run the owner 3/3 and kernel 4/4 focused specs with `--mode=interpreter --no-session-daemon`; require both PASS before trap wiring. |
| Host adapters | Headless adapter, hosted input adapter/stream specs, SDL2 synchronous compatibility present, configuration snapshot selection, and environment/runtime guards have focused PASS evidence. | Win32 and Cocoa submit pixels but deliberately leave `present-awaiting-host-completion`; no true asynchronous host fence producer closes those frames. X11/Wayland/SimpleOS producers and remaining consumers are unproven. | `SIMPLE_LIB=src bin/simple test test/02_integration/os/sosix/headless_display_adapter_spec.spl --mode=interpreter && SIMPLE_LIB=src bin/simple test test/02_integration/os/sosix/sdl2_display_adapter_spec.spl --mode=interpreter && SIMPLE_LIB=src bin/simple test test/02_integration/os/sosix/win32_display_adapter_spec.spl --mode=interpreter && SIMPLE_LIB=src bin/simple test test/02_integration/os/sosix/cocoa_display_adapter_spec.spl --mode=interpreter` |

Highest-impact independent next gap: connect syscall 134/135 in the
architecture-neutral kernel syscall/VFS owner to one persistent
`SosixFsPositionedDispatchOwnerV1`, authenticated caller identity, registered
buffer lifecycle, and the existing true positioned backend. This closes the
production POSIX/VFS path without touching QEMU, ARM-specific code, or the
compiler. Acceptance requires read and write success, stale generation,
foreign owner, bounds, partial-progress/error, shared-offset invariance, and
no seek-emulation scenarios through the focused commands above.

Implementation update: `kernel_positioned_dispatch_v1.spl` now provides the
architecture-neutral persistent install/dispatch state and returns ENOTSUP
until a ready owner is explicitly installed. It recognizes only IDs 134/135,
accepts kernel-authenticated caller identity, and carries the registry and
request token only through returned values; it introduces no globals, raw
pointers, or seek emulation. Verification is RED at the mandatory three-cycle
cap: 2/4 focused scenarios pass. The successful backend/registry transition is
visible, but the deployed interpreter retained token `11`; the final patch now
reconstructs every nested owner layer and computes token `12` at the kernel
boundary, but was deliberately not rerun after the cap. Do not install this
state in a production trap-runtime lifecycle owner until all focused scenarios
pass. Resume exactly once in a fresh session with
`SIMPLE_LIB=src bin/simple test test/01_unit/os/sosix/fs_kernel_positioned_dispatch_v1_spec.spl --mode=interpreter`.
### Fresh Linux parallel evidence — 2026-08-12

Four freshly rebuilt rows were launched concurrently under TCG from
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/direct-parallel-four-20260812/`.
The result is diagnostic RED, not admission: x86_32 reached only its legacy
synthetic PASS path; x86_64 was rejected by QEMU's kernel loader as an ELF64
image; ARM64 mounted FAT then used the stale root `/HELLOSMF.SMF` route; RV32
booted but could not read the target nonce. ARM32 and RV64 did not launch
because their fresh builds hit the bounded three-cycle cap. The immutable
matrix therefore remains 0 PASS / 24.

x86_64 follow-up exhausted its three-cycle descriptor cap. Replacing `-kernel`
with raw and then ELF-parsed loader devices removed the immediate format error,
but both bounded boots produced no serial and timed out. The retained final
transcript hash is
`d64fb9ac2da79dc63c185e0584fd200faacc5a9fa6c420b6b18f9af623f6aa0d`.
Resume only after statically reconciling ELF entry/PT_LOAD addresses with q35
loader/reset semantics; do not repeat either launch command.
