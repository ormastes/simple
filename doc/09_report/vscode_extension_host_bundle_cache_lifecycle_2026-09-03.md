# VS Code Extension Host Bundle Cache Lifecycle

## Problem

`@vscode/test-electron` treats an `is-complete` marker as sufficient evidence that a cached VS Code archive is usable. The observed cache contained that marker but lacked `Visual Studio Code.app/Contents/MacOS/Electron`, so Extension Host startup failed with `ENOENT`. A fresh 1.136.0 archive confirmed that the current executable is `Visual Studio Code.app/Contents/MacOS/Code`; the dependency still returned the legacy `Electron` path.

## Implementation

- Store reusable VS Code test bundles only below `<SIMPLE_USER_STORAGE_ROOT>/cache/vscode-test/bundles`.
- Validate that a regular executable exists before reuse.
- Recognize current `Code`, legacy `Electron`, stable, and Insiders layouts, including archives with one additional root directory.
- Delete incomplete cache entries before attempting reuse.
- Download into a unique staging directory and publish the verified version directory with an atomic same-filesystem rename.
- Preserve and reuse a valid concurrently published winner instead of deleting it.
- Pass the verified executable to `@vscode/test-cli` through `useInstallation.fromPath`.
- Fail closed and remove staging data when validation or publication fails.

## Verification

Deterministic Node fixtures cover current and legacy macOS executables, direct and nested layouts, incomplete-marker removal, atomic publication, and fail-closed staging cleanup.

The single live Extension Host attempt had network access, downloaded VS Code 1.136.0 successfully, and then failed closed before activation because the first validator recognized only the dependency's legacy `Electron` path. The downloaded archive was inspected and established the `Code` executable layout used by the final implementation. The host test was not retried, honoring the one-attempt gate; deterministic final validation covers the corrected layout.
