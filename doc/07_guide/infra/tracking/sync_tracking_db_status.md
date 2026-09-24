# Syncing tracking DB status columns with their record files

## Audit registration before changing lifecycle state

Run the read-only registration owner from a complete checkout:

```sh
sh scripts/check/check-tracking-doc-registration.shs --selftest
sh scripts/check/check-tracking-doc-registration.shs
```

It scans bug and TODO Markdown recursively, recognizes explicit unresolved
Status values without requiring an `OPEN (Pn)` spelling, and reports orphan
documents, missing exact bug documents, malformed row widths, and duplicate
IDs. It ignores fenced examples and generated indexes. Numeric TODO rows may
point directly to source; they do not need a dedicated Markdown document.
A marker-only TODO note is reported for owner triage without assigning a status.

Bug document identity is its basename. An underscore/hyphen date near-match is
only a diagnostic candidate, not an automatic alias or permission to merge IDs.
Multiple rows citing one cluster document are not automatically duplicates.
Review source-only legacy bug records before deciding whether to author an
explicit mapping. The current database schema has no alias or platform columns.

Exit 0 means a complete scan without findings, exit 1 means findings remain,
and exit 2 means the scan was incomplete. The inherited registration backlog
currently makes the full audit fail; the fixture suite can pass independently.
The audit is an operator command, not a newly enabled CI merge gate.
See [the dated audit](../../../09_report/tracking_registration_audit_2026-09-21.md)
for exact records and the scope of platform classification.

Missing documents, deleted source paths, changed TODO wording, or source fixes
do not establish implementation completion. Preserve lifecycle values while
repairing registration. Do not run the status mutation command below as part
of a registration-only audit. Closure requires the owning record's acceptance
evidence and an explicit lifecycle decision.

`scripts/check/sync-tracking-db-status.shs` — `sh scripts/check/sync-tracking-db-status.shs [--root DIR] [--dry-run] [--selftest]`

## What it does

`doc/08_tracking/bug/bug_db.sdn` and `doc/08_tracking/todo/todo_db.sdn` are
supposed to mirror the record files that are the real source of truth (per-bug
`.md` docs; the `# TODO:`/`# FIXME:` comments in source and tracking docs). In
practice they drift apart by hand edits, and on 2026-09-12 five separate agents
independently re-derived the same diff by hand to unblock their own lanes. This
tool automates exactly that reconciliation, one-way, status-column-only:

- **Bug side:** for every row of the `bugs` / `bugs_active` tables whose id has
  a matching `doc/08_tracking/bug/<id>.md`, read the record's first
  status-bearing line (same extraction `check-bug-status-consistency.shs`
  uses — same regex, same "Generated:"-doc skip, same markdown-emphasis
  strip) and map it: `RESOLVED`/`FIXED` -> `fixed`; `CLOSED`/`CLOSED-STALE`/
  `WONTFIX`/`DUPLICATE`/`SUPERSEDED` -> `closed`; `OPEN` or anything else ->
  leave the row alone. Only the `status` column of a matching row is ever
  written; no other column, no row added or removed.
- **Todo side:** todo-scan itself is broken (segfaults after DB write and
  renumbers ids — see
  `doc/08_tracking/bug/todo_scan_segfaults_after_db_write_and_renumbers_ids_2026-09-12.md`)
  so it cannot be used to re-derive `todo_db.sdn`. Instead: for every row, if
  its `file` no longer exists, or exists but no longer contains the row's
  `description` text anywhere in it (quote-style drift and a stable leading
  `(tag)` anchor are both tolerated — see Known limitation below), the row is
  closed. A row whose marker is still findable is left untouched even if its
  current status looks wrong; the tool only ever closes, never reopens, and
  never renumbers or adds rows.
- **Reseal:** `bug_db.sdn` is CRC-32/ISO-HDLC-stamped
  (`#sdn-crc32:<n>` header, see `reseal-sdn-crc32.shs`) and a hand-edited body
  that isn't resealed makes the whole db load as nil. `todo_db.sdn` carries no
  such header. The tool detects this at runtime (checks the actual first line)
  rather than assuming it, and reseals only a db that is actually stamped.

## When to run it

- After a batch of bug docs got their `Status:` line updated (fix landed,
  triaged closed/duplicate/wontfix/superseded) without the corresponding
  `bug_db.sdn` row being touched.
- After code/doc edits removed `# TODO:` comments that `todo_db.sdn` still
  lists as `open`.
- Routinely as a dry-run health check (`--dry-run` never writes anything) to
  see how far the dbs have drifted, before deciding whether to apply.

Always run `--dry-run` first and read the change list; `--selftest` (which
also runs automatically before every real invocation) proves the fixed/closed
mapping, the todo marker-gone->closed path, and the reseal.

## Why hand edits drift

Both dbs are hand-maintained tables inside a plain-text SDN file, edited by
whichever agent happens to be fixing the underlying bug or todo at the time.
Nothing enforces that a `Status:` edit in a `.md` doc also touches
`bug_db.sdn`, or that removing a `# TODO:` comment also flips its `todo_db.sdn`
row to `closed` — there is no single writer, and (for todos) the one tool that
could re-derive the table mechanically is currently broken. The db and the
record files are two independent artifacts that happen to describe the same
fact, and independent artifacts drift unless something periodically
reconciles them. That is this tool's whole job, and only that job — it does
not triage, does not re-open anything, and does not touch any column beyond
`status`.

## Known limitation: curated `todo_db.sdn` rows with no literal-text anchor

Most `todo_db.sdn` rows come from a scan of a real `# TODO:`/`# FIXME:`
comment at a real line, so "is the description still in the file" is a
reliable presence check. A distinct minority are hand-curated backlog notes
attached to a file at `line: 1` (an "owner directive"/summary style entry
referencing multiple files, not a single scanned comment) — for these there
was never a guarantee the exact description text appears anywhere literally,
so the tool treats `line == 1` with no textual match found as **inconclusive,
not gone**, and leaves the row untouched rather than risk closing real open
work. This was found empirically on 2026-09-12: id 280
(`doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md`) has a
real `# TODO: (sosix A5) ...` comment that was reworded in place while
staying open — full-text search alone would have called it "gone" — rescued
here by the stable leading `(sosix A5)` tag.

**Not fully solved:** id 292 in the current tree points at
`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:622` with a
*real* (non-1) line number, yet the comment now at that file is about a
completely different topic (`rt_*` symbol link precedence, not sqlite). This
is the same failure mode (comment reworded/moved, row not re-derived) but
without a `line == 1` or `(tag)` signal to catch it, so this tool still
reports it as "gone" on a `--dry-run`. Filed as
`doc/08_tracking/bug/todo_db_description_drift_false_positive_2026-09-12.md`.
**Any `--dry-run` output from this tool should be read before applying, not
applied blindly** — this is a heuristic over free text, not a proof.
