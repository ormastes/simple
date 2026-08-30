# Bootstrap fail-fast hides independent compiler diagnostics

**Status:** FIXED — owner `codex-bootstrap-diagnostic-sweep` resolved 2026-08-02
**Area:** bootstrap diagnostics / compiler process isolation

## Problem

A staged bootstrap stops at the first compiler failure, so independent source
files are never checked and additional actionable errors remain hidden until a
later retry. Repeated retries waste bootstrap time and serialize bug discovery.

## Required behavior

- Provide an explicit diagnostic-only bootstrap mode.
- Check every independent selected `.spl` file even after failures.
- Group captured diagnostics by file and return nonzero when any file fails.
- Preserve per-file incremental caches and isolate cache writers.
- Retain a source-hashed manifest, exact compiler identities, per-file logs and
  terminal results, and a completion receipt after failure or interruption.
- Treat a compiler signal or timeout as one file outcome and continue through
  the end of the manifest; distinguish a real signal from an ordinary exit with
  the same shell status.
- Never deploy or admit an artifact from the diagnostic mode.
- Cover one failure beside a success and aggregation of multiple failures.

## Resolution

`--diagnostic-sweep` routes bootstrap diagnosis through independent `check`
processes. The runner finishes every selected file, emits grouped failure logs,
summarizes passed/failed counts, and returns `1` when any fail. Stable per-file
cache directories preserve incremental state and isolate parallel writers. The
bootstrap entry rejects deployment/release/full-CLI combinations, and the
diagnostic runner has no artifact output path.

The runner now defaults to `src/compiler`, `src/lib`, and `src/app` and retains
`manifest.tsv`, `results.tsv`, `summary.env`, compiler hashes, and per-source
logs below the selected output. `complete=true` is published only when every
manifest row is terminal. Cleanup retains partial evidence with
`complete=false`.

The integration contract covers exact and adjacent failures, an ordinary exit
139, a real SIGSEGV, post-crash continuation, timeouts and descendant cleanup,
nonzero aggregate status, deterministic terminal rows, parallel cache
separation, and cache preservation. Canonical build/admission behavior remains
fail-fast; this diagnostic mode still has no artifact output path.
