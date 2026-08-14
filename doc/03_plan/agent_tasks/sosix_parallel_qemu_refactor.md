# SOSIX parallel QEMU refactor plan

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

## Plan-level implementation blockers

The detailed ownership/unblock record is
[`sosix_qemu_matrix_remaining_owners_2026-08-14.md`](../../08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md).
In addition to the row blockers, L0 remains open for three fail-closed repairs:

1. The collector must publish a pending/blocked promotion status whenever any
   accepted row is `blocked` or `unsupported`; a file-validation PASS cannot be
   confused with 24-row matrix completion.
2. Nonce-media preparation must reject identical resolved source and run-image
   paths before any copy/move operation.
3. Compiler-in-filesystem validation must use the row's admitted runtime
   identity, never a hardcoded `bin/simple` or seed-adjacent substitute.

These are implementation blockers, not permissions to weaken the 24-row
contract. They keep L0 and the umbrella feature incomplete after this plan
document is handed off.

## Parallel lanes

| Lane | Scope / exclusive owner files | Current state | Acceptance evidence | Sidecar | Merge owner | Final reviewer |
| --- | --- | --- | --- | --- | --- | --- |
| L0 shared matrix | settings, admission, producer, collector, matrix docs | plan complete; implementation blockers open; full-CLI verification WARN | self-tests; one pre-admitted bundle per changed schema; collector reject unless exactly 24 | N/A | root | root/high |
| L1 Linux x86_64 | x86_64 OVMF/GRUB fs-exec entry and boot artifacts | canonical PASS | OVMF→GRUB→guest-entry, real listing, mounted program stdout, exit37/reap/PASS | N/A | root | root/high |
| L2 Linux ARM64 | ARM64 direct-kernel fs-exec entry, nonce reader and EL0 lifecycle | canonical PASS | direct-kernel v2 bundle, exact ordered serial lifecycle | N/A | root | root/high |
| L3 Linux RV32 | RV32 direct-kernel trap lifecycle and nonce media | canonical PASS | direct-kernel v2 bundle, M-mode recovery and exact reap | N/A | root | root/high |
| L4 Linux RV64 | RV64 compiler operand transport, then live fs-exec | blocked | admitted compiler must lower named/immediate asm operands; fresh rebuild then canonical run | N/A | compiler owner | root/high |
| L5 Linux x86_32 | First establish an i686 CPL3 build profile that includes the parent SimpleOS tree, `src/os`, and `src/lib`; then own GDT/TSS/`esp0`, authenticated token, `enter_user_first`, trap return, and mounted ELF staging | blocked | i386 link gate proves strong entry/TSS/token symbols before any QEMU; then live iret/int80/exit37 continuation plus exact scheduler reap | N/A | x86_32 kernel owner | root/high |
| L6 Linux ARM32 | Own real `enter_user_first.s`, exception-vector/SVC entry, token/result lifecycle in baremetal C, scheduler binding, and mounted ELF staging | blocked | ARM link gate proves vector + EL0 entry symbols; then real vector/TTBR lifecycle, target listing/program and exact reap | N/A | ARM32 kernel owner | root/high |
| L7 Windows | PowerShell matrix execution and native producer | blocked external host | actual Windows admission plus all six bundles; no Linux relabeling | N/A | Windows operator | root/high |
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
| `SOSIX-WINDOWS-X86_64` | BLOCKED | native Windows executor, QEMU/media, and a producer-backed guest-run phase (the current peer is preflight-only) | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest x86_64 -Preflight` | `windows/x86_64/<run-id>/evidence.env` or typed blocker | Windows operator |
| `SOSIX-WINDOWS-ARM64` | BLOCKED | same Windows native-run prerequisite | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest arm64 -Preflight` | `windows/arm64/<run-id>/evidence.env` or typed blocker | Windows operator |
| `SOSIX-WINDOWS-RISCV32` | BLOCKED | same Windows native-run prerequisite | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest riscv32 -Preflight` | `windows/riscv32/<run-id>/evidence.env` or typed blocker | Windows operator |
| `SOSIX-WINDOWS-RISCV64` | BLOCKED | same Windows native-run prerequisite | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest riscv64 -Preflight` | `windows/riscv64/<run-id>/evidence.env` or typed blocker | Windows operator |
| `SOSIX-WINDOWS-X86_32` | BLOCKED | same Windows native-run prerequisite | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest x86_32 -Preflight` | `windows/x86_32/<run-id>/evidence.env` or typed blocker | Windows operator |
| `SOSIX-WINDOWS-ARM32` | BLOCKED | same Windows native-run prerequisite | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -Guest arm32 -Preflight` | `windows/arm32/<run-id>/evidence.env` or typed blocker | Windows operator |
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

The Windows commands above intentionally stop at the current fail-closed
preflight. After the Windows peer gains the producer-backed guest-run phase,
the operator repeats the same row with `-Run`; preflight output is never a row
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
  sixth interface; Windows resumes with `-AllGuests -Preflight`, while `-Run`
  remains conditional on implementing producer-backed guest execution.
- Generated-manual applicability: accepted as N/A because this plan-only lane
  changes no executable SSpec or generated manual contract.

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
