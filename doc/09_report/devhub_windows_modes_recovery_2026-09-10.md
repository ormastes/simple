# Windows mode recovery, 2026-09-10

STATUS: PARTIAL — ordinary selection and explicit unsupported loading are
verified; functional loading and Wacatac classification remain outstanding.

## Forensic scope

The interrupted work was in `C:/Users/ormas/dev/simple-launch-modes`, based on
`fe80fe09642470c251870134cb8deb182ea3ce0f`: one modified `bin/devhub` and six
untracked requirement, NFR, architecture, detail-design, test-plan, and
agent-plan documents. It had no executable mode tests. The proposed external
loader interface had no in-tree implementation. Direct `--version` and
`--help` runtime admission also contradicted AV-blocked runtime recovery.

In `simple-combined-integration`, every dirty tracked path except
`examples/05_stdlib/spipe/package.json` is originally a mode-120000 symlink.
Observed directory junctions and hardlinked file contents support build
materialization, including apparent compiler aliases and debug/lint/cert
source changes. The package change adjusts Node tests/concurrency and is
outside this recovery. Neither original worktree was edited or reverted.

Recovery uses `simple-windows-modes-recovery`, branch
`work/windows-modes-recovery-20260910`, based on the remote combined-integration
commit above. The recovered design removes claims of successful loading and
replaces nonexistent test references with the implemented shell harness.
There is no externally configured loader dispatch and no antivirus bypass.

## Verification evidence

- `sh test/00_unit/scripts/devhub_windows_launch_modes_test.shs`: PASS on
  Windows with Git for Windows sh. Actual fixture processes verify default
  and explicit ordinary mode, argument spaces, CLI precedence, verbose
  dispatch, loading exit 78 without probes, invalid/missing modes exit 2,
  child failure status 41 with one dispatch, and stale hash rejection.
- Existing `devhub_windows_launcher_test.ps1`: PASS for explicit shell
  override/argument forwarding and missing-shell exit 127. Its discovery
  branch SKIPPED because sh.exe was absent from that process's PATH; this
  is not claimed as a passing real-shell CMD integration scenario.
- `git diff --check`: PASS. Executable `*_spec.spl` count under `doc/06_spec`:
  zero. Working-tree direct-env runtime guard: PASS.

Fixture receipts exercise repository identity admission only. They do not
prove native PE startup, loading support, vendor signatures, antivirus
classification, complete bootstrap, or deployment. No full bootstrap or
push was performed in this lane. The design skill drove the explicit
unsupported boundary instead of accepting the interrupted loader contract.
