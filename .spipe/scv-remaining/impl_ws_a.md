# SCV Workstream A — Implementation Notes

## What Was Done

Three files were changed to fix the PROD-001 interpreter memory-pressure failures.

### 1. `src/lib/scv/public_remote.spl` — Pre-existing parse error (root blocker)

The file used invalid Simple syntax for a struct definition:
```
struct ScvRemoteRef {
    branch: text,
    commit: text,
    artifact_dir: text,
}
```
Fixed to valid Simple struct syntax:
```
struct ScvRemoteRef:
    branch: text
    commit: text
    artifact_dir: text
```
This was introduced in commit `4f67b0ae`. It caused `src/app/scv/main.spl` to fail
compilation on every child invocation, making all 5 assertion tests return `exit=1`
(not an OOM issue at all — a parse blocker).

### 2. `test/integration/app/scv_wasm_executor_spec.spl` — Memory env vars

Added `SIMPLE_MEMORY_LIMIT_MB=1024 SIMPLE_SIBLING_PRELOAD_LIMIT=5` to every
`bin/release/simple` invocation in all 6 `it` block shell scripts.

- `SIMPLE_MEMORY_LIMIT_MB=1024` enables the watchdog, so RSS overruns produce a
  clean diagnostic instead of a silent kernel OOM kill with truncated stdout.
- `SIMPLE_SIBLING_PRELOAD_LIMIT=5` reduces sibling eager-loading from 20 to 5,
  cutting the module explosion multiplier. SIMPLE_LIB remains `$REPO/src` (single
  search root required by the path resolver).

### 3. `test/integration/app/scv_wasm_executor_spec.spl` — AC-1e sed pattern fix

The AC-1e script extracted the grammar hash via:
```sh
sed -n 's/.*|parser_hash=\([^|]*\).*/\1/p'
```
But `parse-index` output is positional pipe-delimited; there is no `parser_hash=`
label. The grammar artifact hash lives in `parsers` output (field 7 of `parser|…`
rows). Fixed to:
```sh
parsers 2>/dev/null | awk -F'|' '/^parser/{print $7}' | head -1
```

## Result

All 6 tests pass consistently across two runs:
- AC-1a: locked grammar bytes load from .scv/parsers by hash
- AC-1b: parse results carry execution=fallback-line when wasmtime shim is absent
- AC-1c: fallback execution is used when wasmtime dynlib is absent
- AC-1d: parser failures allow private snapshot to proceed
- AC-1d edge: corrupt WASM grammar produces execution=fallback-line not crash
- AC-1e: grammar hash change invalidates parse-gate cache

## Note on the Research Hypothesis

The original research hypothesis (OOM-kill under concurrent load) was correct as a
*potential* risk but was not the *actual* failure mode in the tests. The immediate
cause was a parse error in `public_remote.spl` (invalid `struct { }` syntax) that
blocked all child process compilations. The memory env vars are belt-and-suspenders
for concurrent test environments and are correct to add regardless.
