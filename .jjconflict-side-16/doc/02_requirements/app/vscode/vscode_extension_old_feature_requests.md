# VS Code Extension Old Feature Requests

The legacy `src/app/vscode_extension_old` package was removed after comparison with the active
`src/app/vscode_extension` package. The active package already carries the user-facing commands,
settings, LSP fallback surface, AI commands, math preview/sync panel commands, test workspace
commands, and editor marker commands from the old extension.

Deferred old-only items to reconsider if demand returns:

- Rebuild the old dedicated `math-core.wasm` pipeline as an active extension feature only if native
  TypeScript math rendering proves insufficient for parity, performance, or browser-host behavior.
- Restore broader old E2E labels (`lsp-e2e`, `ai-e2e`, `integration`) as maintained tests against
  the active extension. The current active test harness covers GUI/math/marker behavior, but the
  old package described larger LSP and AI suites that were not present as active maintained tests.
- Recreate old packaged VSIX/release scripts (`vsce package`, `vsce publish`) in the active package
  only when the extension release flow is revived.
