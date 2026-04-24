# Bootstrap stdlib parse failure from `//` tokenization - 2026-04-24

## Status

Fixed.

## Summary

A host-side compiler warning reported:

`Failed to parse module path=".../src/compiler_rust/lib/std/src/infra/file_io.spl" error=Unexpected token: expected expression, found Parallel`

The warning was real, but the actionable root cause was narrower than the message implied:

- the bootstrap/interpreter parser tokenizes `//` as the `Parallel` operator
- `infra/file_io.spl` and `infra/parallel.spl` both started with a `// stdlib primitive boundary...` header
- that leading token sequence was parsed as `Parallel`, not as a comment

This was not a `parallel.spl` import bug and not a stale loader cache issue.

## Root cause

The stdlib files used a comment form that is not safe on this parser path.

Relevant parser behavior:

- `//` is a real language token for parallel execution
- the bootstrap path therefore does not treat `// ...` as a line comment
- the first such header in a loaded stdlib file can fail parsing before any useful context is emitted

The misleading part of the investigation was the diagnostic wording. The error named `infra/file_io.spl`, while the token kind was reported as `Parallel`, which initially suggested sibling-module preload drift rather than a bad leading token in the file itself.

## Fix

Changed the leading primitive-boundary headers from `//` to `#` in:

- `src/compiler_rust/lib/std/src/infra/file_io.spl`
- `src/compiler_rust/lib/std/src/infra/parallel.spl`

Also fixed the separate stdlib export warning by making `io.fs_helpers` exports public and restoring a public compatibility alias:

- `src/compiler_rust/lib/std/src/io/fs_helpers.spl`

## Verification

The following commands were used as the narrow and broad checks:

```bash
bin/simple os targets
bin/simple os test --scenario x64-desktop-uefi
sh scripts/check-core-runtime-smoke.shs bin/simple
SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs
```

Observed outcome after the fix:

- `bin/simple os targets` no longer emits the `found Parallel` warning
- `x64-desktop-uefi` still passes strictly
- core runtime smoke passes
- native MCP/LSP smoke passes

## Follow-up guidance

For stdlib and bootstrap-sensitive source files, prefer `#` line comments in file headers and primitive-boundary markers. Do not use `//` as a comment marker on paths that may be parsed by the bootstrap/interpreter toolchain.
