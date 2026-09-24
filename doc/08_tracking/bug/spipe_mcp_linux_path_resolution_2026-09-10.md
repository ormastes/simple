# SPipe package: Linux Node path resolution depends on Node 20-only metadata

- **Date:** 2026-09-10
- **Status:** fixed by `spipe_mcp_export_linux`
- **Severity:** P2 (Linux Node 18 package tests fail before exercising Unicode fixtures)
- **Area:** `examples/05_stdlib/spipe/test/unit/unicode_17_tables_test.js`

## Pre-fix reproduction

On the Linux-compatible Node 18 path, after the export blocker is isolated,
loading the Unicode table test fails before its first test:

```text
TypeError [ERR_INVALID_ARG_TYPE]: The "paths[0]" argument must be of type string. Received undefined
    at resolve (node:path:1097:5)
```

The test uses `import.meta.dirname`, which is not available in Node 18. The
package supports the same Node runtime used by the MCP stdio server, so test
path setup must derive the directory from `import.meta.url`. Once that path
setup is corrected, the adjacent generator check exposes the same Node 18
compatibility boundary: `Array.prototype.toSorted` is unavailable and fails
with `TypeError: ranges.toSorted is not a function`.

## Boundary and plan

This is a test/package JavaScript path-compatibility defect; it does not alter
the MCP server's canonical POSIX-relative path contract. The fix uses the
standard `fileURLToPath(import.meta.url)` plus `dirname` conversion and a
copy-sort fallback for the Node 18 generator. A POSIX fixture-resolution
regression and an adjacent Windows-separator negative assertion remain
separate.
