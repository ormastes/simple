# Browser/Wasm IDE Parity Slice

## Scope

This slice closes the missing VS Code fixture and makes browser/Wasm degradation explicit without changing the KPF ABI generator or compiler lint implementation.

## Result

- Desktop and browser hosts use one canonical Simple document selector, including `vscode-vfs`.
- LSP lifecycle state publishes a typed capability receipt distinguishing authoritative semantic coverage from syntax-only fallback coverage.
- Degraded fallback messages explicitly state that results are not semantic-clean evidence.
- Diagnostics, symbols, and semantic-token service statuses follow the same authoritative/degraded receipt.
- The configured VS Code `test-workspace` now contains a canonical Simple fixture exercised through the shared fallback analysis index.

## Verification

- `npm run compile`: PASS.
- Host-independent compiled capability-receipt assertions: PASS.
- Focused VS Code GUI selection was attempted after repairing the downloaded executable alias. The host remained blocked before extension activation because its generated IPC socket path exceeded macOS's 103-character limit; no GUI PASS is claimed.
- `git diff --check`: PASS.
