# Private streamed preparation and explicit publication

Design frozen 2026-10-04 at release
`02e4836a820507d8bdf38f1feea31c44c649ee92`.
Owner/session: `/root/linker_research`, `item4-stream-prepare-docs-20261004`;
worktree `C:/dev/simple-item4-stream-got-docs-20261004`, branch
`work/item4-stream-prepare-docs-20261004`. Only this document is owned here.
Runtime owns implementation, acceptance owns specifications, root integrates;
sidecars N/A. No runtime execution or release qualification is claimed.

## Existing behavior and selected seam

`src/compiler/70.backend/linker/elf/stream_link.spl` currently opens retained
inputs, plans the image, checks simultaneous original/spill/replay scratch,
emits a private image, syncs and closes input/output handles, stages checked
spill, and immediately publishes to the caller's destination.
`src/lib/nogc_async_mut/link_working_set/file_store.spl` replays and validates
spill before `file_publish_noreplace`. Its successful publication returns
committed bytes and cleanup status; a cleanup failure must not become an
apparent pre-commit failure.

The split belongs immediately after successful spill staging. Preparation
must accept no destination. It performs real linking and retains private
cleanup ownership without modifying the final output. This is an additional
production lifecycle seam, not a replacement linker or a worker admission.

## Frozen API and ownership

`elf_stream_prepare_file_v1(objects, archives, entry, scratch_parent, limits,
cancelled)` returns `Result<ElfStreamPreparedV1, text>`. Arguments retain their
existing types. The prepared owner stores mutable `stage:
Option<LinkStagedFileV1>`, private-image `directory`, and
`publication_attempted` latch.

`me elf_stream_publish_prepared_v1(output, cancelled)` returns the existing
`Result<ElfStreamLinkResultV1, text>`. Before destination validation or any I/O,
the first attempt burns the publication right. All later attempts fail,
including after invalid destination, cancellation, corrupt spill, no-replace
failure, or cleanup failure. No error path restores that right.

On successful commit, move the remaining stage/directory cleanup state into
`ElfStreamLinkResultV1`, clear the prepared owner, and report actual
`published_bytes` and `cleanup_pending`. The existing
`me elf_stream_cleanup_result_v1()` owns subsequent committed-output cleanup.
Post-commit cleanup trouble must remain a successful committed result.

`me elf_stream_discard_prepared_v1()` performs independent cleanup retries.
It retires publication even if cleanup fails, clears each owned resource only
after its cleanup succeeds, and is idempotent when already empty. A failed
publication retains whatever cleanup capability remains; failed cleanup does
not make publication reusable. Both directories should receive cleanup attempts
so one blocked resource does not prevent independent cleanup of the other.

This latch is needed because current spill failure cleanup can leave
`consumed=false`, and a changed stage directory can return directly. A raw
spill stage alone therefore does not enforce one publication attempt.
Use explicit `me` mutation and optional-owner take/writeback; do not mutate
copies through free helper parameters. Public class/value copying remains a
caller discipline, not language-enforced linearity, security, or IPC authority.

## Compatibility and remaining failure boundaries

`elf_stream_link_file_v1` delegates real preparation and publication, preserving
its signature, no-replace behavior, existing quota arithmetic, cancellation,
and successful result cleanup API. Preserve early output-path validation in
this compatibility wrapper so invalid legacy calls do not acquire inputs.
The new owner independently validates its later destination after burning the
latch. The wrapper must attempt disposal after publication errors and report
remaining cleanup paths honestly.

Preparation-time errors inside existing open/emission/staging helpers still
return text. Some cleanup failures there lack a typed retryable owner. This
wave does not repair that lower-level error contract or claim complete cleanup
on every preparation failure. Logical scratch reservations also remain distinct
from filesystem capacity, RSS, descendants, or no-swap enforcement.

## Executable acceptance obligations

Tests use canonical `std.spec.step`, real ELF fixtures and independently checked
output bytes. Filesystem setup assertions must guard subsequent mutation.

1. Prepare actual inputs without a destination; inspect owned private artifacts,
   then publish and validate ELF headers, segments and relocated values.
2. An existing destination sentinel survives no-replace failure; a second
   publication to another path fails without producing that path.
3. Cancel after preparation, then publish: no output; publication remains spent;
   discard cleans remaining resources.
4. Mutate an actual spill frame before publication: integrity error and no final
   output; no second publication succeeds.
5. Place an unexpected file in a private stage directory to prevent directory
   removal after commit. Publication returns success with cleanup pending;
   remove the obstacle and clean through the existing result owner. Final
   output bytes remain unchanged.
6. Combine that obstacle with a pre-existing destination: publication errors,
   retains cleanup state, refuses retry, and permits cleanup after obstacle
   removal. Do not simulate cleanup success with a Boolean callback.
7. Discard before publication prevents publication. Repeated empty discard is
   successful. Discard retry after a real obstacle clears only actual resources.
8. Preserve one-shot wrapper bytes/no-replace/cancellation/quota behavior and
   verify returned cleanup state transfers out of the prepared owner.

Authoring, source review, execution, generated manuals, branch coverage and
host qualification are separate evidence. Simple execution remains UNRUN.

## Future worker and all-host obligations

A future admitted worker may prepare privately, but this in-process owner is
not a transferable capability. Cross-process artifact identity, bounded wire
protocol, retained authority, parent-owned validation/publication, before-exec
resource controls, descendant collection and trusted admission remain required.
`UnsupportedBudget` remains correct until an enforcing path exists. See
`resource_evidence_and_worker_2026-10-04.md` for those obligations.

User scope requires native runnable support on Windows, Linux, SimpleOS,
FreeBSD and macOS. This lifecycle extraction inherits existing retained-file,
no-follow directory and no-replace publication platform owners. It does not add
missing host primitives or prove native execution on any host. The root host
matrix must track each owner's availability and actual native acceptance;
cross-produced ELF/Mach-O/PE bytes do not substitute for host execution. In
particular, hosted filesystem assumptions must not be inferred for SimpleOS.

Simple's mold-style linker stays explicit opt-in; external hosted selection
remains the default. Target-specific SimpleOS routing remains separate. No
automatic selection or qualification follows from adding this API.
