# Test manifest invalidation is size-ONLY — the "mtime" column is a second copy of the size

Status: OPEN (P1)
Filed: 2026-08-17 (lane CACHE)
Engine: `bin/simple test` via `bin/release/x86_64-unknown-linux-gnu/simple`.
Scope: the **spec-file** side of the test manifest (`.simple/test-manifest.idx`,
`manifest.entries`). The **doctest** side is NOT affected — see "Who needs to
care" at the bottom.

## Headline

The manifest's incremental-update predicate is documented and written as
"unchanged iff size AND mtime match". It is actually **size AND size**. The
mtime half is a no-op, so any edit that preserves a file's byte count is
invisible to the cache, and no `touch -r` is required to defeat it.

`src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl:81-82` (specs) and
`:97-98` (sdoctest rows):

```
val current_mtime = rt_file_stat(f)
...
if (old_entry.path != "" and
    old_entry.file_size == current_size and
    old_entry.file_mtime == current_mtime):
```

`rt_file_stat` does not return an mtime:

- `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:289-294` —
  doc comment says *"Get file stat info (simplified - returns size or -1)"*,
  body is `Ok(Value::Int(meta.len() as i64))`.
- `src/runtime/simple_core/core_fs.spl:396-400` — SimpleOS guest version returns
  the constant `0`, with its own `ponytail:` note that this "disables cache
  freshness".

A real mtime accessor exists and is unused here:
`rt_file_stat_mtime` (`file_io.rs:2477`).

**Empirical proof** — every manifest produced during this investigation has the
size and "mtime" columns identical, because they are the same call:

```
test/01_unit/cachelane/skipped_spec.spl|162|162|1|0|1|0|||0|0|0|0|0|0
test/01_unit/cachelane/alpha_spec.spl|160|160|1|0|0|0|||0|0|0|0|0|0
```

## Reproducer (executed 2026-08-17, isolated scratchpad sandbox)

The sandbox has its own `.simple/test-manifest.idx`; the shared tree's manifest
was never touched. TTL is 300 s (`test_manifest.spl:61`,
`MANIFEST_TTL_MICROS = 300000000`); freshness gate is
`test_runner_files.spl:263`.

```sh
mkdir -p SB/test/01_unit/cachelane && cd SB
# alpha_spec.spl  : plain spec, first line "# plain"
# skipped_spec.spl: same spec, first line "# @skip"
bin/simple test test/                       # R1
```

R1 (rc=1, captured on the line after the command, never through a pipe):

```
[setup] discover: 46ms (1 file(s))
Results: 1 total, 0 passed, 1 failed
```

manifest: `entry_count=2`, `skipped_spec` `skip=1`, `alpha_spec` `skip=0`.

Then three mutations at once, and `scan_timestamp` rewritten to "now" so the
rerun lands inside the TTL (this is the only field altered — it emulates a
second run within 5 minutes, which a real short run gets for free):

1. `# @skip` -> `# @keep` in `skipped_spec.spl` — **byte size unchanged, 162**
2. new file `gamma_spec.spl` created
3. `alpha_spec.spl` **deleted from disk**

R2 (rc=1):

```
[setup] discover: 27ms (1 file(s))
FAIL  test/01_unit/cachelane/alpha_spec.spl (0 passed, 1 failed, 312ms)
Results: 1 total, 0 passed, 1 failed
```

| # | case | expected | observed | verdict |
|---|------|----------|----------|---------|
| 1 | size-preserving edit un-skips a test | test becomes visible | still filtered out; entry still `skip=1` | **FAIL** |
| 3 | new spec added inside the TTL | discovered | never discovered, never run | **FAIL** |
| 4 | spec deleted from disk | entry dropped | **discovery selected and dispatched the deleted path** | **FAIL** |

Post-R2 manifest still lists the deleted `alpha_spec.spl` and the stale
`skip=1` row.

### Caveat, stated rather than papered over

In case 4 the phantom surfaced as a **FAIL**, not a green pass, because the
scratchpad harness cannot spawn a child spec process (exit 127). A *green*
phantom — a deleted test reported as passing — is therefore **UNPROVEN**, not
disproven. The load-bearing fact is upstream of the verdict: discovery selected
and dispatched a path that does not exist. What the child then reports is the
child's business, not the cache's.

Cases 2 (bulk move without `--refresh-manifest`) and 5 (concurrent mid-scan
mutation) were **not executed** — budget. They are not covered by this record.

## Why the TTL does not save you, and why it also does not always expose you

`discover_test_files_fast` (`test_runner_files.spl:262-269`) falls back to a full
slow scan when the manifest is stale or does not cover `base_path`, so a run
more than 300 s after the last scan discovers correctly. But the manifest it
then writes goes through `manifest_incremental_update`
(`test_runner_files.spl:381-386`), which re-applies the broken size==size test —
so the stale rows are **carried forward indefinitely** even by runs that
themselves discovered correctly. Staleness is not self-healing; only
`--refresh-manifest` (`test_runner_main.spl:232-241`, `manifest_full_scan`)
clears it.

Measured side note: R1 on a two-file tree took long enough that the manifest was
**already 314 s old — past its own TTL — by the time it finished**. On the real
tree the fast path is therefore reached less often than the design assumes,
which is the only reason this has not bitten harder.

## Who needs to care: SPEC side yes, DOCTEST side no

`manifest.sdoctest_entries` is written and exported but has **zero selection
consumers**. The only readers outside the manifest modules are
`test_runner_main.spl:226` (the `--manifest-status` printout) and a length
comparison in `manifest_daemon.spl:63`. `sdoctest/discovery.spl` performs a live
`dir_walk` on every run and never consults the manifest at all. Lane TOOL
reached the same conclusion independently from the discovery side.

This is the same shape as `watcher/smf_manifest.spl:134`'s
`smf_manifest_entry_verifies`: exported, plausible, wired to nothing. The
consequence is asymmetric and worth stating plainly — **doctests are immune to
manifest staleness because they are never cached; specs are fully exposed
because they are cached with a predicate that cannot see content changes.**

## Fix sketch (NOT applied — not small, needs its own red-first change)

1. Point the scanner at a real mtime source (`rt_file_stat_mtime`, or a new
   `rt_file_mtime` extern) so `file_mtime` stops being a duplicate of
   `file_size`. Bump `MANIFEST_VERSION` — every existing on-disk manifest has a
   size in the mtime column and must be discarded, not reinterpreted.
2. Size+mtime still cannot catch a same-size, same-mtime edit. A content hash of
   the metadata-bearing region, or an interface digest in the
   `interface_digest_of` spirit, is what actually closes case 1.
3. Existence-check every carried-over entry in `manifest_incremental_update`
   before pushing it. This alone kills case 4 and is genuinely small.
4. `manifest_full_scan` on a root that is a prefix of an existing root should
   drop the subsumed rows rather than merging them.

Guard landed with this record: `scripts/check/check-doctest-manifest-staleness.shs`.

## This is live on the shared tree right now, not only in a sandbox

`sh scripts/check/check-doctest-manifest-staleness.shs` run read-only against
`/mnt/data/worktrees/simple-main` on 2026-08-17 (rc=1, manifest md5 unchanged
before/after: `6796318759316d52d0976f939d89b3a9`):

```
FAIL  scanner-mtime: .../test_manifest_scanner.spl uses rt_file_stat() (5 site(s))
FAIL  manifest-columns: all 20126 row(s) have size == mtime
FAIL  manifest-existence: 111 of 20126 path(s) do not exist:
      .tmp_probe/a_spec.spl .tmp_probe/b_spec.spl
      test/01_unit/compiler/50.mir/hwir_riscv_scalar_runtime_*_spec.spl ...
```

**20126/20126 rows have size == mtime** — the fingerprint is total, exactly as
predicted from the source. And **111 entries point at files that no longer
exist**, including probe paths from other lanes' scratch dirs. Case 4 is not a
sandbox artefact; the shared manifest is carrying 111 dispatchable phantoms
today. (The roots line is also polluted: it contains `800`, `.tmp_probe`, an
absolute `/mnt/data/tmp/...` scratch path and `build/failopen_probe` — a
separate arg-plumbing defect, not filed here.)
