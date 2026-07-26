# Stage 4 CLI entry-closure resolver candidate remains unverified without a manifest-attested full CLI

- **ID:** `stage4_cli_entry_closure_resolver_probe_unverified_2026-07-26`
- **Date:** 2026-07-26
- **Area:** `src/app/io/_CliCompile/compile_targets.spl`,
  `_native_build_entry_closure`
- **Severity:** high candidate — it may block the pre-QEMU guest native-build
  investigation and therefore SimpleOS x86_64/ARM64 evidence preparation.
- **Status:** OPEN — no qualifying timing evidence is retained in this
  worktree; no speculative source patch is accepted until it can preserve the
  real closure under a qualifying tool.

## Unverified handoff observation

The task handoff reports the following planning baseline for a frozen
`0cec853a8a` full-CLI closure probe with
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`:

| bounded wall time | latest trace receipt |
|---:|---|
| 10 seconds | `closure visited 50 queued=163` |
| 30 seconds | `closure visited 75 queued=255` |

It also reports that the traversal had not reached compiler-driver start at
either boundary. The raw 10-second/30-second command, binary hash, and logs
are not retained in this worktree. The only local attempt was stopped when its
CLI identified as a Rust seed before the walker; the local bootstrap Stage 3
binary rejects `run`. Therefore this table is an **unverified scheduling
observation**, not measured performance evidence, a successful build, or an
accepted Vulkan/QEMU result.

## Source-level candidate hot path

The walker avoids duplicate exact resolved-path strings and memoizes normalized
slash-joined absolute-module keys in `resolve_cache`; that does not prove
physical-file deduplication. Each cache miss still repeats filesystem resolver
work:

1. `_native_build_entry_closure` (`compile_targets.spl:573`) turns every
   absolute import into `mp.split(".")` and joins the segments for a cache
   key. It performs a second shortened-path lookup only when the primary
   resolution is empty and the import has more than one segment (`:628-640`).
2. `_nb_resolve_segs` (`:510`) calls `_driver_resolve_entry_import` only for a
   `compiler.*` path with more than one segment (`:514-522`). It then
   canonicalizes the resolved candidate and each source root with
   `rt_path_absolute` before it can decide whether the numbered path is
   admissible.
3. The ordered source-root loop tries stripped-root resolution only when the
   first segment matches the root (or the `std`/`lib` alias, `:526-534`); it
   probes direct-root resolution only when that conditional lookup did not
   return (`:535-537`). `_nb_resolve_under_root` is declared at `:495` and
   constructs/probes three candidates at `:498-507` (`.spl`, `/mod.spl`,
   `/__init__.spl`) with `rt_file_exists`.
4. Only after all ordered-root probes miss, `_nb_source_dirs_cover_workspace`
   recomputes its three root-membership checks when `segs.len() > 0` (`:538`).
   When coverage is incomplete it probes `src` (`:539-541`); only after that
   does the unconditional `src/lib` direct fallback run. The six tier fallbacks
   occur only for `std.*` imports with more than one segment (`:551-560`).

The order is semantic: it selects concrete source ownership, determines which
physical path is queued, and thereby controls module identity, membership,
ordering, and later compiler diagnostics. Relative imports must also remain
per-importer rather than be folded into a global module-path cache.

## Why no source rewrite was retained

An apparent optimization would precompute normalized root paths and an indexed
candidate table, then cache all filesystem probes. That is not safe to accept
from a source-only comparison: the current cache distinguishes empty
resolution from an absent cache entry, the numbered compiler resolver has an
admissibility check against the caller's exact roots, and fallback order is
observable in closure ordering and errors.

The only deployed full CLI available during this diagnosis identified itself as
a Rust bootstrap seed and was stopped before it reached this walker. The
available frozen `bootstrap/stage3/simple` identifies as `simple-bootstrap`
and has no `run` command, so it cannot execute the checked-out source or the
optimizer application. Neither artifact is valid evidence for a production
Simple-only optimization. No Rust/C fallback, source edit, SPipe placeholder,
or synthetic timing was used.

## Required next experiment

Before changing `compile_targets.spl`, produce a full CLI from the same frozen
source with a standalone-PASS Stage 3 provenance manifest. Use the exact
manifest-selected full-CLI path and output hash, never ambient `bin/simple`.
The manifest must bind frozen source, the Stage 3 producer and its manifest,
the ordered roots, complete backend/runtime command, and full-CLI output hash.
The selected binary must be a pure-Simple full CLI (not
`bootstrap/stage3/simple`) and must execute both `run` and `optimize`.

Then, in one isolated cache/worktree:

1. Reproduce and record the reported 10-second and 30-second baseline with the exact
   `--entry`, ordered `--source` roots, backend, runtime bundle, and compiler
   hash. Preserve every `closure visited` line.
2. Add a `test/05_perf/compiler/` SPipe regression that compares each real
   fixture's exit status, complete ordered closure path list, and full
   diagnostics byte-for-byte against its expected values. Its assertions must
   cover duplicate imports, empty cached misses, numbered compiler imports,
   `std.*` tier fallback, and importer-relative paths; it must contain no
   placeholder pass.
3. Apply only an order-preserving root/index or probe memoization change. After
   proving both command surfaces on the exact manifest-selected CLI path/hash,
   run `MANIFEST_SELECTED_CLI run src/app/optimize/main.spl
   src/app/io/_CliCompile/compile_targets.spl --full --level=O3`, then the new
   SPipe test and the existing native-build cache/entry-closure contracts.
4. Repeat the identical 10-second and 30-second trace. Accept the change only
   if every fixture's status, complete ordered closure, and diagnostics are
   byte-for-byte identical, and the last emitted trace receipt is no earlier
   at either identical boundary and strictly later at one. First reproduce the
   candidate handoff values (`visited=50, queued=163` at 10 seconds and
   `visited=75, queued=255` at 30 seconds) under the qualifying CLI. If they
   differ, retain and use the qualifying baseline and update this report.
   Retain the raw command, manifest-selected binary hash, timing, and logs.

Until those gates pass, the stage4 full-CLI closure diagnosis in
`stage4_full_cli_closure_spin_2026-07-18.md` remains authoritative. This
report identifies source-level resolver/probe candidates; it does not claim
their timing contribution, or that resolver work is the sole Stage 4
bottleneck.
