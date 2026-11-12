# native-build parse shard SIGSEGVs when `SIMPLE_HIR_CACHE_DIR` points at a fresh empty dir

- Status: open (deterministic repro; no root cause yet)
- Found: 2026-11-13
- Component: `native-build` parse shard cache path
  (`src/compiler/80.driver/driver_hir_cache.spl`, parse-shard startup)
- Binary: stage2-admitted pure-Simple compiler
  (`sha256=3a795fed8f12…`), pinned source `5e217d7fd0e`,
  macOS aarch64 24 GiB

## Repro

```
cd <pinned source tree>
S=$PWD/.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/simple
SDKROOT=/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX26.2.sdk \
MACOSX_DEPLOYMENT_TARGET=15.0 \
SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 SIMPLE_BINARY=$S \
SIMPLE_HIR_CACHE_DIR=/tmp/hir-probe-cache \
$S native-build --source src/lib --entry-closure \
  --entry src/lib/editor/services/diagnostics.spl --output /tmp/diag_probe
```

Deterministic (2/2 runs): immediately after `source_closure` completes
(67 files), the parse shard dies:

```
[parse-shard] shard=0/2 pid=<n> FAILED exit=-139
[parse-shard] shard=0/2 pid=<n> dead-child cleanup: kill=false
```

System memory free: 85% (not a resource kill). The identical command with
`SIMPLE_HIR_CACHE_DIR` unset (default machine cache root, warm entries)
parses the same closure fine:

```
[parse-fibers] files=28 parsed=28 done=28 errors=0 import_parks=0 cache_hits=26 cache_misses=2
[parse-shard] shard=0/2 pid=<n> exit=0
```

## Impact

Any lane that isolates the HIR cache with a fresh dir (diagnostic capture,
cache-quarantine probing, cold-cache timing) dies in the parse shard before
compilation starts. The bootstrap lanes use the default warm root, so the
matrix gate is NOT affected by this bug directly.

## Notes

- `-139` = SIGSEGV in the shard child. No crash report line is emitted by
  the harness beyond the exit status.
- Suspect surface: the parse cache's cold-dir initialization path (dir
  creation is fine — `hir_cache_dir()` + `rt_dir_create_all`), more likely
  a cold parse-cache index/segment write or a missing nil-check when the
  cache index is absent.
- Same-command probe with `SIMPLE_HIR_CACHE_SELFCHECK=1` and the default
  cache dir ran past parse; selfcheck capture is tracked in
  `phase2_matrix_hir_cache_decode_refusal_missing_module_surface_2026-11-12.md`.

## Fix direction

Run the shard under lldb with the fresh dir, get the faulting frame, and
nil-check the cold cache-index path. Add a smoke: fresh-dir parse of a
2-file closure must not crash (regression test belongs next to the existing
hir-cache store tests).
