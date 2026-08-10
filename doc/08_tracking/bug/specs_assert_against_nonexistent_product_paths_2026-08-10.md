# Specs assert against product files that do not exist — negative legs pass vacuously (2026-08-10)

Status: **RED / OPEN**. 835 specs reference 949 distinct product paths that are
absent from the committed tree. Two rename clusters are fixed (see Fixed
below); the remaining ~849 paths are DELETED or NEVER-EXISTED and their specs
are deliberately left RED.

## The shape

A spec reads a product path that is missing. The read returns empty content.
A **negative** leg then passes against that emptiness:

```
val src = read_file("src/compiler/80.driver/driver/incremental.spl")   # gone
expect(src.contains("legacy_cache_key")).to_equal(false)               # VACUOUS PASS
```

This **overturns a rule that several prior streams and their briefs treated as
sound**: "negative / absence assertions cannot be vacuous." They can. Absence
assertions are vacuous exactly when the subject they assert absence *in* is
itself absent. The prior exclusion was wrong and any vacuity census that
carried it under-counted.

Positive legs (`to_contain`, `to_equal(true)`) fail loudly on a missing file,
which is why this shape hid: it only ever manifests on the negative leg, and a
green negative leg looks like a satisfied invariant.

## Detection

`scripts/check/check-spec-missing-path-vacuity.shs` — fail-closed, three
controls in a fatal `--selftest` that runs before every scan (planted missing
path MUST be flagged; an existing path MUST NOT be; a path appearing only in
the spec's own comment MUST NOT be harvested). Verdict line last on stdout;
zero specs examined is `ERROR` exit 2, never a pass. Mutation proof: disabling
path extraction turns the selftest into `ERROR -- nothing was checked` exit 2.

Whole-corpus run: `FAIL -- 19614 specs checked, 2305 missing-path references`.

Full census: `doc/08_tracking/test/spec_missing_path_census_2026-08-10.tsv`
(`<spec>\t<missing path>`, 2004 rows after excluding `bin/release/**` build
outputs).

## Classification

- **RENAMED** — the file moved; the reference is stale. Tractable, fixed below.
- **DELETED** — the capability is gone. The spec asserts about something that
  no longer exists. Left RED: whether the spec or the product is wrong is a
  per-site product decision, not a mechanical edit.
- **NEVER EXISTED** — the strongest finding: the spec was written against an
  **imagined harness**. `git log` on the path is empty. Confirmed examples from
  the Q24 stream: `scripts/qemu_rv64_http_test.shs` and
  `scripts/qemu_rv32_http_test.shs`, referenced by
  `simpleos_riscv_network_gate_spec.spl`, were never committed at any point in
  history. Left RED.

Exhaustive per-path RENAMED/DELETED/NEVER-EXISTED labelling of all 949 paths is
NOT yet done and must not be assumed: a whole-history `git log --all
--name-only` harvest exceeded 6.8 GB and was aborted before it could exhaust
the disk (ENOSPC has wiped `main` twice in this repo). Per-path `git log` on a
scoped subset is the workable method.

## Fixed

- `doc/06_spec/test/**` -> `doc/06_spec/**` (the `test/` segment was dropped
  from the generated manual tree). 25/25 references resolve. 3 specs.
- `examples/simple_os/**` -> `examples/09_embedded/simple_os/**` and
  `examples/ide/**` -> `examples/10_tooling/ide/**`. 108 references, 35 files
  including duplicate-tree twins. Only references whose renamed target was
  confirmed present were rewritten; non-resolving ones were left RED rather
  than guessed.

## Left RED (not weakened)

Everything else in the census, including:

- `native_build_cache_plumbing_spec.spl` — the whole
  `src/compiler/80.driver/driver/` directory is gone (DELETED).
- `simpleos_riscv_network_gate_spec.spl` — `scripts/qemu_rv{64,32}_http_test.shs`
  NEVER EXISTED.
- `.spipe_wrapped_entry_qemu_runner_spec.spl`,
  `scripts/check-heavy-work-preflight.shs`.

No spec was weakened, skipped, or softened.

## Follow-up

1. Label the remaining ~849 paths RENAMED/DELETED/NEVER-EXISTED using scoped
   per-path `git log`, not a whole-history harvest.
2. Re-run any prior vacuity census that excluded negative/absence assertions —
   its exclusion is disproved.
3. Wire `check-spec-missing-path-vacuity.shs` into the gate once the backlog is
   burned down; it FAILs the whole corpus today.
