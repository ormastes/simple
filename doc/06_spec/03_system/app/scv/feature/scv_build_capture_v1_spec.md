# Managed SCV build-input capture V1

Source: `test/03_system/app/scv/feature/scv_build_capture_v1_spec.spl`.
Audience: SCV and BuildRunner maintainers.

Execution: **NOT_RUN**. The tests were committed before the implementation;
there is no admitted general test/docgen CLI in this session. This authored
manual is a review aid, not a generated or executed SPipe receipt. Runtime
red/green, docgen and sspec-maintain admission remain outstanding.

## Exact managed input bytes

REQ-SCV-BUILD-CAPTURE-01 freezes actual supplied binary payloads, including NUL
and non-ASCII bytes, without decoding them as text. Mutating the caller's byte
array, complete scopes, external roots, queued editor transaction, or a returned
read buffer must leave the retained snapshot unchanged. Generated, external and
configuration entries retain their exact bytes and declared origin.

This is an in-process logical owner. The caller declares the complete managed
universe and supplies exact configuration, environment, target, compiler and
runtime digests. A constructor cannot prove that a physical filesystem or
editor has been observed. A physical producer must reconcile that universe
and report coverage holes rather than infer watcher acknowledgement from an
inventory generation.

## Identity and path policy

REQ-SCV-BUILD-CAPTURE-02 binds every entry's path, kind, numeric mode, binary
content, origin and producer digest, together with all universe fields and the
capture cursor. Entry/scopes/root order is canonical. Configuration-only,
environment-only, executable-mode and producer-only changes produce distinct
identities even when source content stays the same.

REQ-SCV-BUILD-CAPTURE-03 permits only the exported V1 path-policy digest and
`managed-build-inputs-v1` namespace. Paths are exact-case relative logical UTF-8
paths with slash separators. Traversal, empty components, control characters,
duplicate paths, overlapping complete scopes, unknown kinds/modes and regular
file ancestors are refused. External entries must lie under explicitly declared
external roots; another origin cannot occupy that namespace.

Allowed kinds and modes are regular (420/493), directory (493, empty payload)
and symlink (511, nonempty exact target bytes without NUL). Origins are
committed, worktree, editor, generated, external and configuration. Every entry
requires a lower-case 64-digit SHA-256 producer binding. Those bindings express
the parent producer identity, not compiler semantic authority.

## Resolution and absence

REQ-SCV-BUILD-CAPTURE-04 reads copied regular-file bytes and lists sorted direct
directory children, including implicit parents and explicit empty directories.
Missing paths within a complete scope return `build-path-absent`; paths outside
the declared universe return `build-path-unknown`. Creating a child changes an
empty directory's result while older frozen snapshots retain the old negative.

Symlink target bytes are retained and hashed, but reads/listing through a
symlink fail with `build-symlink-resolution-unsupported`. Directories fail a
regular-file read. The legacy `ScvSnapshotV2` projection contains regular files
only. Directory and symlink entries remain explicit unsupported inputs and
force that projection's coverage to `unknown`; the new full logical universe
does not manufacture legacy source-resolution capability.

## Ordered capture barrier

REQ-SCV-BUILD-CAPTURE-05 opens an owner at sequence zero and applies transactions
through `scv_build_capture_apply_v1(state, expected_cursor, transaction_id,
changes)`. Acknowledgement requires exact state CAS and the next sequence in the
same epoch. An identical transaction-ID replay is idempotent; changing the
payload under that ID is refused. Puts explicitly replace the previous entry,
with no inferred editor/disk precedence. Deletes require an existing path and
remove every captured descendant of an explicit directory.
Renames require the exact previous entry digest and refuse occupied targets,
descendant cycles and regular destination parents. An explicit directory rename
moves every captured descendant atomically.

`scv_build_freeze_v1(state, expected_cursor)` requires the latest exact
acknowledged cursor and drains every acknowledged transaction before returning
the snapshot. Older barrier requests fail; consumers retain older snapshots
when they need historical bytes. Pending state is capped at 1024 transactions;
a full reconciliation begins a new epoch.

## Coverage holes and tampering

REQ-SCV-BUILD-CAPTURE-06 rejects cursor gaps, epoch changes, replay collisions,
corrupt snapshot content and noncanonical array order. A producer that sees a
gap, dropped event, overflow or incomplete reconciliation must replace its
owned state with `scv_build_capture_unknown_v1(state, reason)` and retain it.
Because this is a value API, ignoring an `Err` cannot mutate an older retained
state. The parent must never treat that older state as the producer's current
acknowledgement after an error.

An unknown state refuses both transactions and freeze. Only explicit complete
managed reconciliation through `scv_build_capture_reconcile_v1` in a fresh epoch
restores a usable owner. Snapshot validation rebuilds the complete canonical
subject and checks the legacy projection; a caller-supplied complete boolean,
digest string or reordered array cannot grant authority.

## Integration and performance boundary

The parent owns actual editor/filesystem ingestion, durable publication and
worker byte delivery. This module creates no scheduler, watcher, daemon,
compiler-semantic receipt or physical I/O fallback. Public DTOs are mutable
values, so read/list APIs validate their complete subject before serving bytes
or absence. Queue admission likewise validates the retained transaction chain.
Large-universe throughput and RSS have not been measured; no performance or
production-readiness claim is made from authored specs alone.
