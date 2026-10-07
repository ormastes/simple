# SCV snapshot repeats recursive creation at every ancestor

Status: isolated source candidate; native qualification pending.

The completed e73 Hello cold run took 433.37 s, with the snapshot receipt
appearing about 343 s after invocation. Its warm run took about 108 s. These
observations identify snapshot publication as a cold-start cost, but do not
attribute all of it to this bug. Empty HIR worker startup and the remaining
post-HIR time are separate issues.

`scv_compile_snapshot_materialize_source_unscoped_v1` called
`scv_create_parent_dir(destination)` for every inventory member. That helper
splits an absolute path and calls `dir_create(prefix, true)` for each ancestor.
The Windows runtime's `rt_dir_create_cpath` already recursively walks every
ancestor, issuing `CreateDirectoryW` and, for existing directories,
`GetFileAttributesW`. Combining both loops repeats ancestor work quadratically
in destination depth. The Simple loop also allocates intermediate prefix text.

The candidate changes only the snapshot caller to extract the parent at the
last slash and invoke recursive creation once. Snapshot staging is owned and
the relative source path has already passed `scv_worktree_path_safe`, so the
destination always has a parent slash. Existing physical containment, source
digest, chunk publication, destination digest, source-drift and receipt checks
remain in place. Creation failure still reaches the existing file-write failure
and the outer snapshot owner removes its stage. No directory-success cache or
longer-lived allocation is introduced. General store helper semantics remain
unchanged.

## Evidence and qualification

`scripts/check/scv-parent-create-operation-bench.py` compares both operation
patterns using actual Windows directory APIs in private temporary fixtures.
It runs five fresh-process paired samples for cold and existing directories,
records directory call counts, time, traced allocations, process peak/steady
RSS, script hash and Python hash, and checks that every parent exists. This is
an API-operation model, not a Simple compiler/runtime or whole-build speedup.
The evidence schema explicitly sets `native_simple_qualified=false`.

Measured on the Windows host with 256 destinations at the same depth:

| Operation-model metric | Baseline | Candidate |
| --- | ---: | ---: |
| Directory creation calls | 23,552 | 3,328 |
| Cold p50 / p95 seconds | 6.402 / 6.603 | 0.855 / 0.939 |
| Existing-parent p50 / p95 seconds | 6.525 / 6.612 | 0.876 / 1.024 |
| Cold process peak bytes | 21,651,456 | 21,630,976 |
| Existing-parent process peak bytes | 21,602,304 | 21,598,208 |
| Maximum traced scratch bytes | 1,333 | 785 |

Cold time/memory ratios are 0.1423/0.9991 (sum 1.1413); existing-parent ratios
are 0.1549/0.9998 (sum 1.1548). RSS differences are measurement noise, not a
demonstrated process-memory reduction. Five-sample p95 is the maximum sample.
All parent-existence checks passed. Retained evidence is
`scv-parent-create-operation-model.json` in the Windows restart packet root.
These measurements must not be reported as an 85% compiler startup improvement.

`test/01_unit/lib/scv/compile_snapshot_parent_creation_spec.spl` exercises the
real materializer for missing deep Unicode parents, sibling reuse, exact CRLF
bytes and a parent blocked by a sentinel file. Native execution is pending.
The existing `compile_snapshot_reclamation_spec.spl` and
`test/05_perf/scv/compile_snapshot_resource_profile_spec.spl` remain the native
memory and resource acceptance gates. Existing provisional producers currently
fail unrelated provider lowering; no identical failing full build is justified
to qualify this small change. No native performance improvement is claimed
until those gates run with a usable pinned producer.

## 2026-10-06 Windows Phase4 follow-up

Old7404 Phase4 on source f2f87a21 (source606 plus seven unrelated import/export repairs) reached source-inventory publication approximately463seconds after native start, then snapshot/receipt publication at806seconds and shard admission afterward. These are observed filesystem/log boundaries, not CPU-stack attribution or a controlled benchmark. The repeated recursive-parent owner remains in both bc9 and e50f; the live e50f producer build is not restarted. Reuse2270's source fix/tests in the next candidate. No hashes, source drift checks, scratch ownership, or authority publication checks are removed. Full native memory/performance qualification remains pending.

The ordinary Git-snapshot preparation helper has a separate analogous cost:142189blob writes/readbacks (2.41GB) took307.99seconds. Its per-file `dest.resolve().is_relative_to(S.resolve())` repeatedly resolves root/ancestors; repeated mkdir(parents=True) also revisits known directories. A future helper change may bind the canonical root once and cache validated owned parent directories, but must still check each destination containment and reject reparse/drift before use, retain exact blob hashes/readback, and bound parallel buffered bytes. This is a source-proven repetition, not a measured share of307.99seconds; no active materializer is changed.
