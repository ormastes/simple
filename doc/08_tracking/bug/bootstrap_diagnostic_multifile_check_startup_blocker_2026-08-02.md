# Bootstrap diagnostic multi-file check startup blocker

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Area:** bootstrap diagnostics / check entrypoint / interpreter startup

## Live evidence

The optimized diagnostic sweep still spends minutes per file. A representative
live worker had this process shape:

- Rust seed parent: about 91 MiB RSS, 0.4% CPU, waiting;
- delegated production child:
  `bin/release/x86_64-unknown-linux-gnu/simple run src/app/check/main.spl <target>`;
- child: about 278 seconds elapsed, 60% CPU, and 231 MiB RSS.

At 32 workers this is approximately 7.4 GiB of concurrent child RSS. The raw
`run` entrypoint recompiles/loads the check app and its compiler-parser import
closure for every target. `SIMPLE_NATIVE_BUILD_CACHE_DIR` isolates writers but
does not turn this interpreted/raw-source startup into a cached executable.
This is why the observed cost is far above one second per file.

No measurement identifies AOP as the dominant cost. The live command has no
AOP-specific mode or flag, and the repeated cost occurs before the tiny target
parse can explain the elapsed time. Current evidence supports duplicated
Pure-Simple `run` startup/import-closure/interpreter work, not an AOP claim.

## Multi-file investigation

The documented surface says `simple check <file.spl> [file2.spl ...]`, but the
production `src/app/cli/check_entry.spl` does not execute one multi-file worker.
It expands the targets and calls `process_run_timeout` inside a `for file` loop,
constructing `run src/app/check/main.spl <one-file>` each time. Therefore a
12-file public check still launches 12 expensive workers; it cannot provide a
meaningful batching speedup benchmark.

The underlying `src/app/check/main.spl` can accept multiple files. It calls
`ast_reset()` before each parse, continues after failures, and aggregates the
result. However, its JSON contract contains only aggregate counts. Human output
contains diagnostic text but is not a complete machine-readable terminal row
for every file. If a chunk fails or times out, the sweep cannot prove which
files completed, which passed, or which file retained a descendant. Treating
the whole chunk as failed would misattribute good files; treating unmentioned
files as passed could miss diagnostics.

Because exact attribution and all-file coverage are release-safety properties,
chunking is not enabled. A synthetic 12-file fake-worker benchmark would only
measure a scheduler model, not the supported production command, and is not
reported as production evidence.

## Safe stronger design

Build one diagnostic-only check-runner artifact keyed by:

- check app source/import-closure fingerprint;
- compiler binary identity;
- target/runtime family and build flags.

The artifact must remain under the diagnostic cache, never be admitted,
deployed, or used as a Stage compiler. It should accept a sorted manifest and
emit an append-only terminal record for every file (`id`, encoded path,
pass/fail, error count). It must reset parser, AST, lexer, diagnostics, and any
semantic globals between files. The sweep can then run bounded manifest chunks
in separate process groups and preserve the existing timeout/grace/KILL rules.
An interrupted chunk may requeue only IDs lacking a terminal record. Each
artifact/cache writer remains isolated or uses a single-writer atomic publish;
workers consume the resulting artifact read-only.

## Required proof before enabling

1. Exact and adjacent tests with pass/fail/pass ordering and state-poison probes.
2. A timeout after at least one terminal row, proving only unfinished IDs retry.
3. Descendant-held-output cleanup and deterministic source-order reporting.
4. Artifact fingerprint invalidation and concurrent single-writer publication.
5. A 12-or-more-file production benchmark against one-file dynamic mode,
   including startup time, per-file latency, max RSS, and identical diagnostics.

Until those proofs exist, per-file process isolation is slow but correct.

## 2026-08-04 reproduction

The robust lifecycle persistence verification lane reproduced the blocker with
`simple check src/compiler`. The default 60-second CPU guard killed the first
delegated checker at 64 seconds. With `SIMPLE_TIMEOUT_SECONDS=300`, the next
delegated checker remained CPU-bound for more than two minutes while the parent
had not advanced past the first compiler file. The bounded run was terminated
and its logs retained under `build/verify_robust_lifecycle/`; extrapolating this
per-file startup across the compiler tree is not a viable release check.

## Cached executable build attempt

Compiler identity:
`e0a2fcc63bd3dc4ba27e0630b294208f1a984f0eab51621d973fdbabb2930bd5`.
Checker source identity:
`b6a84359e311d298c1f398f27cd631a20f3e833588f65bea25e4021ad02dfb25`.

The first bounded native build used a positional entry, expanded outside the
intended closure, and reached the 300-second timeout without an artifact. The
corrected cache-preserving command used explicit
`--entry src/app/check/main.spl --entry-closure --mode dynload`. It reused the
first attempt's object cache and reached link in 23 seconds, but link failed
with missing core-runtime symbols:

- `rt_array_sort`
- `rt_env_remove`
- `rt_is_debug_mode_enabled`
- `rt_dir_list`

The selected `core-c-bootstrap` runtime explicitly refuses hosted fallback.
No executable exists, so cold/warm checker wall time, files/s, RSS, process
count, diagnostics checksum, and exit parity are **not measurable**. Reporting
source/interpreter timings as native checker results would be false. The kept
objects and logs are diagnostic evidence only; they are not admitted or
deployed.

The final allowed cycle selected the supported `host-gpu` hosted lane (not a
stub or fallback) because the canonical Rust runtime archives define all four
symbols. It reused the object cache and stopped after 9,599 ms at link, with a
maximum RSS of 228,136 KiB and no artifact. The runtime archive selector accepts
`<runtime-path>/bootstrap/deps/libsimple_runtime.a`, but
`find_hosted_runtime_rlib` checks only `<runtime-path>` and
`<runtime-path>/deps`. With `--runtime-path .../target`, the former archive was
found while the canonical hosted rlib at
`.../target/bootstrap/deps/libspl_hosted_runtime-*.rlib` was reported missing.
Using `.../target/bootstrap` would align both selectors, but a fourth build was
not run because the mandatory three-cycle cap had been reached.

## Static selector resolution

Hosted runtime archive and rlib discovery now share one normalized authority
search contract. A target root searches the root, `deps`, `bootstrap`, and
`bootstrap/deps`; an adjacent `target/bootstrap` path searches that directory
and its `deps` without producing duplicate nested-bootstrap candidates. Exact
tests cover both accepted path forms and fail closed when neither authority is
present. No additional checker build was run after the three-cycle cap.
