# Watch Mode & Dependency Cache Plan

## Goals
- Provide a `watch` workflow similar to `npm run watch` that recompiles on file changes.
- Track per-source dependencies (imports) and macro identifiers so dependent modules rebuild when a dependency changes.
- Cache dependency info on disk to avoid recomputing everything on every change.

## Design

### Components
- **Dependency Analyzer**: Scans a source file for `import …` statements and `macro …` definitions, emitting a list of dependent paths and macro ids.
- **Build Cache** (`target/simple_watch_cache.json`): Stores `source -> {output, dependencies, macros, mtime}` to drive incremental rebuilds.
- **Watcher**: Uses filesystem notifications to watch the entry directory. On change, finds affected sources via the cache, recompiles to `.smf`, and reruns.

### Flow
1. Initial build:
   - Analyze entry source for deps/macros.
   - Compile to `.smf` (same basename).
   - Save cache entry.
2. Watch loop:
   - On `Modify/Create/Remove` events, gather changed paths.
   - Add any sources that directly depend on those paths (from cache).
   - Rebuild affected sources; update cache with refreshed deps/macros and mtimes.
3. Macro tracking:
   - Macro names are captured (token before `(` or `=`) so changes to macro definitions mark dependents stale.

### Notes
- Paths without extensions default to `.spl`; relative imports resolve against the source file’s directory.
- Cache directory is `target/`, mirroring other build artifacts.
- Rebuild strategy keeps it simple: per-source, re-run compile+load; entry is run after rebuild.
