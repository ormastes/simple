# `src/lib/nogc_sync_mut/mcp/jj/**` imports the nonexistent `app.mcp_jj.*` namespace

- **Filed:** 2026-08-18
- **Status:** OPEN
- **Severity:** P2 — hard error, but the package is dead (no external importer)
- **Tool:** `bin/simple` (Rust **seed**)

## Symptom

Every file in `src/lib/nogc_sync_mut/mcp/jj/` fails to load:

```
$ bin/simple run src/lib/nogc_sync_mut/mcp/jj/helpers.spl ; echo RC=$?
[INFO] JIT compilation failed, falling back to interpreter: semantic: Cannot resolve module: app.mcp_jj.jj_runner
error: semantic: Cannot resolve module: app.mcp_jj.jj_runner
RC=1
```

## Scale

32 `use app.mcp_jj.*` edges across 12 files:

```
$ /usr/bin/grep -rn "use app\.mcp_jj\." --include=*.spl src/ | wc -l
32
$ /usr/bin/grep -rln "use app\.mcp_jj\." --include=*.spl src/ | wc -l
12
```

Imported module paths include `app.mcp_jj.jj_runner`, `app.mcp_jj.helpers`,
`app.mcp_jj.warning`.

## Root cause

There is **no `src/app/mcp_jj` directory anywhere in the tree**:

```
$ /usr/bin/find src -type d -name "mcp_jj*"
(no output)
```

The real targets are immediate siblings of the importers — e.g.
`src/lib/nogc_sync_mut/mcp/jj/jj_runner.spl` defines `class JjResult` at line
11, which `helpers.spl:6` tries to import as `app.mcp_jj.jj_runner.{JjResult}`.

This is the **same module-root defect already filed for
`src/lib/nogc_sync_mut/test_runner/main.spl`**: the module root is the entry
file's directory, so an `app.*` path is unresolvable from a `src/lib/**` entry
file. The package was relocated out of `src/app/mcp_jj/` into
`src/lib/nogc_sync_mut/mcp/jj/` and its imports were never rewritten.

Note the file's own comments still describe the old layout ("Re-exports from
app.mcp.helpers"), while the *code* on line 5 already imports
`std.nogc_async_mut.mcp.helpers` — i.e. the sibling imports were partially
migrated and the `app.mcp_jj.*` ones were missed.

## Liveness — DEAD

- No importer outside the package: `grep` for `mcp.jj` / `mcp/jj` across
  `src/`, excluding the two `mcp/jj/` package directories themselves, returns
  nothing.
- No reference from `scripts/`, `bin/`, or `.mcp.json`.

`.mcp.json` ships `simple-mcp` (`bin/simple_mcp_server`), not an `mcp_jj`
server. So this is an unreferenced island, the same shape as the already-filed
`test_runner/main.spl` case — prevalence without impact.

## Why not fixed in this change

The lane brief permits fixing only small, certain, unambiguous cases with one
clear new path. This is a 32-edge, 12-file subsystem migration. The correct
target for each edge is very likely the sibling module
(`app.mcp_jj.X` -> the local `X`), but rewriting 32 edges across a package
that no one imports, on a dead path, is a deliberate migration that should be
done — or the package deleted — as its own reviewed change. It must not be
silenced by deleting imports.

## Fix options (pick one deliberately)

1. **Rewrite** the 32 edges to the sibling package path and verify
   `bin/simple run` reaches rc=0 on each of the 12 files.
2. **Delete** the package if the jj MCP server is genuinely retired — but only
   after confirming `src/lib/nogc_async_mut/mcp/jj/` (the parallel copy) is
   likewise unused.

Do not do both halfway.

## Related

- The already-filed `test_runner/main.spl` E1034 module-root bug (same root
  cause, different package).
- Census and false-positive analysis:
  `doc/09_report/dangling_import_census_2026-08-18.md`.
