# Live KPF IDE Canonical Conformance — 2026-09-03

## Scope

This lane establishes one live JSON-compatible SDN corpus for native Simple
IDE/SVIM, VS Code desktop, and browser/Wasm client adapters. It also removes
the macOS extension-host IPC blocker without introducing a third storage root.

## Contract

- `src/app/vscode_extension/test-fixtures/canonical-tooling-conformance-v1.sdn`
  is the sole receipt/snapshot fixture.
- Native Simple decodes it with the canonical SDN parser.
- Desktop and browser clients load it through `vscode.workspace.fs`, which is
  valid in both Node and web extension hosts.
- Each adapter proves the same URI, revision, digest, canonical result ID,
  authority, coverage, and semantic-completeness behavior.

## IPC storage

The VS Code test runner derives a short session beneath
`SIMPLE_USER_STORAGE_ROOT`, falling back only to
`SIMPLE_WORKTREE_STORAGE_ROOT`. It exports that session through `TMPDIR`,
`TMP`, and `TEMP`, removes it after the test process settles, and fails closed
when neither of the two approved roots can satisfy the 103-byte macOS Unix
socket budget. No `/tmp` fallback or third authority is introduced.

## Verification

| Check | Result |
|---|---|
| Short two-root socket policy | PASS, 3/3 |
| TypeScript desktop/browser adapters | PASS, `tsc -p ./` |
| Native Simple IDE/SVIM corpus execution | PASS, 6/6 |
| Short session cleanup | PASS, no retained session directory |
| VS Code Extension Host | BLOCKED before activation by a separately broken downloaded application bundle: `Electron ENOENT` |

The prior 103-character socket-path failure is no longer reached: the runner
constructs and exports a bounded path under the centralized roots before the
extension host starts. The downloaded VS Code bundle lacks its expected
`Visual Studio Code.app/Contents/MacOS/Electron` executable, so this report does
not claim end-to-end host PASS.
