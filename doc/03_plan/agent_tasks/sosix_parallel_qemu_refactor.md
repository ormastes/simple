# SOSIX parallel QEMU refactor plan

## 2026-08-14 implementation status

The host-independent L0 repairs are implemented: the collector now reports
`pending` whenever any row is non-PASS, nonce media rejects resolved
source/run aliases before mutation, and compiler-serial validation runs through
the row's admitted `spec_runtime`.  Their focused self-test is
`sh scripts/check/check-sosix-qemu-shared-owners.shs --self-test`.

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
L0 settings/admission/media/evidence
 ├─ L1 x86_64 PASS
 ├─ L2 ARM64 PASS
 ├─ L3 RV32 PASS
 ├─ L4 RV64 compiler fix → runtime closure
 ├─ L5 x86_32 privilege lifecycle → runtime closure
 ├─ L6 ARM32 privilege lifecycle → runtime closure
 └─ L7/L8/L9 actual-host operators
                       ↓
             root collector: exactly 24 bundles
```

## Current-host next sequence

1. Do not rerun L1–L3 unchanged green rows.
2. L4 first requires a clean admitted compiler that transports named and
   immediate inline-asm constraints; the bootstrap seed's debug spelling is not
   an acceptable workaround.
3. L5 first replaces the legacy CPL0 initrd probe entry and proves its i686
   source-root/link closure; L6 first replaces the NVFS/SMF probe with a real
   EL0/SVC owner. Both then proceed only through their frozen scalar trap ABIs;
   do not add untrusted user token pointers, weak dispatch bridges, or host
   test doubles.
4. L7–L9 retain their acceptance IDs as blocked/postponed, with the exact
   target-host commands in the status ledger.

## Implementation handoff — not feature completion

This document-completion lane hands off implementation; it does not complete
the SOSIX matrix feature. Every row without fresh canonical producer evidence
remains active. No release, matrix-complete claim, or collector PASS is valid
until `SOSIX-LINUX-RISCV64`, `SOSIX-LINUX-X86_32`,
`SOSIX-LINUX-ARM32`, all Windows rows, all FreeBSD rows, and all macOS rows
have their own accepted bundle and the collector validates exactly 24 rows.
The table above retains each prerequisite, exact next command, expected output,
execution owner, merge owner, and final reviewer.

## Cooperative review receipt

- Sidecar row audit: completed 2026-08-14; found and required the stable
  24-row IDs, per-row resume contracts, and explicit handoff language now in
  this document.
- Sidecar guide/ownership audit: completed 2026-08-14; required exact shared
  script names, guide/wiki/tracking refresh, producer self-test clarification,
  and the three L0 blockers recorded above.
- Merge owner: `/root`.
- Final high-capability reviewer: `gpt-5.6-sol`, ACCEPTED 2026-08-14 after one
  correction cycle. The review covered AC-1 through AC-9, all 24 unique row
  IDs and states (3 PASS, 15 BLOCKED, 6 POSTPONED), prerequisites, exact
  resumes, artifacts, ownership, the five interfaces, six manual phrases,
  links, expert/tracking knowledge, broad exclusions, and done-mark honesty.
- Review corrections: the ledger is a separate status authority rather than a
  sixth interface. The later 2026-08-16 continuation implemented the Windows
  `-Run` source path and all six distinct collector-nonce readers; native
  Windows verification and all six bundles remain conditional and open.
- Generated-manual status: required by the executable handoff spec, but not yet
  generated because the available self-hosted docgen exits 139. A handwritten
  manual is not accepted as a substitute.

## Plan-document verification receipt — 2026-08-14

The high-capability reviewer performed the focused pass once and did not rerun
unchanged green gates after the correction:

- 24 stable row IDs: PASS (3 PASS, 15 BLOCKED, 6 POSTPONED).
- Every non-PASS row resume/artifact/owner contract: PASS.
- Plan/guide/ledger/expert/tracking link and policy consistency: PASS.
- `sh scripts/setup/install-spipe-dev-command.shs --check`: PASS.
- `find doc/06_spec -name '*_spec.spl' | wc -l`: PASS (`0`).
- `sh scripts/audit/direct-env-runtime-guard.shs --working`: PASS.
- `sh scripts/audit/direct-env-runtime-guard.shs --staged`: PASS.

This is `STATUS: PASS` for the plan-document goal only. It does not change the
implementation handoff or make `SOSIX-MATRIX-COLLECT-24` pass.
