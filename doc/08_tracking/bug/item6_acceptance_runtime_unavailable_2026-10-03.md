# Item 6 acceptance execution lacks an admitted runtime

Date: 2026-10-03. State: OPEN, qualification blocked.
Work branch: `work/item6-dev-20261003`; target: `release/1.0`.
PR: https://github.com/ormastes/simple/pull/2299

## Observed authority

- The primary Windows workspace has no `bin/release` deployment.
- The earlier `simple-item1-bootstrap-20261003` bootstrap log terminates with
  `VERDICT — ABORTED: stage=stage2 exit=1`; its linker failed to resolve
  `rt_fd_stat_snapshot_v1`. No earlier artifact is treated as admitted.
- A separate Windows process, PID 25836 at inspection, is executing a
  `native-build` in `simple-item1-bootstrap-export-20261003`. The executable
  beneath `stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/` has sibling
  `simple.exe.inputs.sha256` metadata declaring
  `schema=simple-bootstrap-seed-artifact-stamp-v2`, with seed digest
  `40c58c6cc30fdbb6650a396eeb84873e7fa1a74baea752d50c137a0f55654233`.
  This is a live build dependency, not an admitted SSpec runner. No process
  was interrupted and no mutable artifact from that lane was executed here.
- Ubuntu WSL has no installed `simple` command or discovered release
  deployment. `/root/simple-build` phase snapshots carry phase1 lineage;
  its `bin/simple.exe` is a Windows PE, not a Linux self-hosted deployment.
- WSL MCP/LSP deployment metadata under `/root/.local/lib/simple/mcp` declares
  `compiler=phase1-rust-seed`. A connector call cannot therefore supply the
  missing self-hosted qualification merely because it returns successfully.
- `%LOCALAPPDATA%/simple/host` supplies configuration, not an executable runner.
  The Windows `bin/simple.cmd` wrapper permits seed fallback and is excluded
  from this qualification path.

These are point-in-time observations, not claims that a live process remains
running indefinitely. Revalidate that process or its terminal receipt before
waiting or using a later artifact. Never restart a bootstrap because an
observation timeout expires.

## Impact and next action

The GC publication exclusion regression was written before its repair, but no
behavioral RED/GREEN was executed. Follow-up reader and persisted-corruption
specifications remain unexecuted. The reader implementation is gated on an
actual baseline failure. The 44 broad system scenarios additionally require the
missing production checker and real filesystem/compile receipts; supplying a
runner alone does not complete them.

Provide an immutable self-hosted runner with lineage/admission receipt and
non-vacuous test capability, or complete the independently owned bootstrap.
Record executable digest, source/toolchain identity and target before executing
the new tests on baseline and candidate. Preserve stage provenance and verify
real assertion counts; a zero exit alone is insufficient.

Remaining qualification includes compiler/lib/MCP/LSP checks, runtime/native
smokes, generated manuals, full production acceptance and existing performance
budgets. No runtime or overall verification PASS is claimed. Draft PR #2299
must not be represented as ready or merged while these gates remain unresolved.
