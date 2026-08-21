<!-- codex-design -->
# SimpleOS Complete OS Hardening — TUI Design

## Operator dashboard

```text
SIMPLEOS HARDENING target=x86_64 env=QEMU-TCG receipt=8f31… [BLOCKED]

[1 Matrix] [2 Blockers] [3 WM] [4 Performance] [5 Artifacts] [q Quit]
Boot PASS   FS BLOCKED   Exec BLOCKED   Toolchain BLOCKED
Servers BLOCKED   Security BLOCKED   WM BLOCKED   Recovery PASS
Rows: 18 PASS / 47 BLOCKED / 0 SKIP   ledger=v1   source=abc123

BLOCKERS
> FS_EXEC_BACKEND_NEUTRAL owner=loader  resume=<exact command>
  LLVM_GUEST_COMPILE      owner=toolchain artifact=<path>
  WM_AARCH64_VISUAL       owner=wm      receipt=MISSING

ARCH / FILESYSTEM / SERVICE
x86_64  OVMF     FAT32 PASS    DBFS BLOCKED  NVFS BLOCKED
AArch64 EDK2     FAT32 BLOCKED DBFS BLOCKED  NVFS BLOCKED
RISC-V  OpenSBI  FAT32 BLOCKED DBFS BLOCKED  NVFS BLOCKED

PERF (native admission only)
WM first frame       231 / 250 ms PASS
input→present p95     27 /  25 ms BLOCKED
FS metadata p95      2.1 / 2.5 ms PASS
```

## Interaction

- Arrow/Tab moves panes and rows; Enter expands immutable row detail.
- `/` filters by requirement, capability, owner, target, filesystem, or status.
- `r` shows the exact resume command read-only; `e` opens receipt/artifact metadata.
- Pointer click selects and wheel scrolls; destructive actions are absent.
- Focus is visible through a cursor plus reverse video; color is never the only status cue.

The dashboard reads a frozen `SimpleOsCapabilityLedgerV1` projection and cannot mutate/promote a row. Missing, stale, malformed, skipped, target-mismatched, or unavailable evidence renders `BLOCKED` with owner and resume data.

## Accessibility and capture

Support high contrast, 80-column reflow, deterministic screen-reader order, no animation-dependent meaning, and textual status labels. Capture bounded ANSI/text under:

`build/test-artifacts/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec/`

The SSpec uses typed `text`/`api` captures and `# @evidence-display: links` for large artifacts.

