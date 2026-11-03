# Bug Database

The bug database is stored in `doc/08_tracking/bug/bug_db.sdn`, an SDN file with CRC32 integrity checking.

## Tables

### bugs_active and bugs
Core bug tracking tables with the same schema:
- **id**: Unique bug identifier (e.g., `native_parser_nested_quotes_2026_10_19`)
- **severity**: P0-P4 priority level
- **status**: open, investigating, fix-implemented-verification-pending, closed, fixed, invalid, resolved-*
- **title**: Short description of the bug
- **file**: Primary source file where the bug manifests
- **line**: Line number in that file
- **reproducible_by**: Model/person who can reproduce it
- **created_at**: YYYY-MM-DD creation date
- **updated_at**: YYYY-MM-DD last update date
- **valid**: Boolean; true if row was formally verified, false if pending review

### bug_descriptions
Extended descriptions for bugs (one or more rows per bug_id):
- **bug_id**: References a bug from bugs_active or bugs
- **line_num**: Sequential line number (0, 1, 2, ...)
- **content**: Full description text, often with reproduction steps and evidence

### bug_difficulty (NEW)
Difficulty assessment and history for bugs. Multiple rows per bug_id allowed (newest assessed_at wins):
- **bug_id**: References a bug from bugs_active or bugs
- **difficulty**: 1-5 scale:
  - 1 = trivial (one-line spec fix, doc typo)
  - 2 = easy (single-site obvious fix)
  - 3 = medium (contained code fix in one module with known cause)
  - 4 = hard (cross-module, compiler/codegen/ABI, unclear root cause, or needs repro)
  - 5 = very-hard (miscompile/concurrency/memory corruption, needs bisect, or blocks bootstrap)
- **basis**: Quoted reason drawn from the bug title/description (e.g., "one-line spec fix")
- **assessed_at**: YYYY-MM-DD assessment date
- **assessed_by**: Model/lane that performed assessment (e.g., haiku-difficulty, sonnet-triage-p1)

### bug_investigation_logs
Investigation notes and findings (one or more rows per bug_id):
- **bug_id**: References a bug from bugs_active or bugs
- **line_num**: Sequential line number
- **content**: Investigation details, workarounds, related issues

### bug_fix_strategies
Proposed and implemented fix strategies (one or more rows per bug_id):
- **bug_id**: References a bug from bugs_active or bugs
- **line_num**: Sequential line number
- **content**: Fix approach, design notes, implementation plan

### strings
Shared string table for efficient storage:
- **id**: Unique string identifier
- **value**: The string content

## Coverage Requirements

All non-closed bugs (status != closed/fixed/invalid/resolved-*) must have at least one row in bug_difficulty.

This is enforced by the coverage check in `scripts/check/check-bug-difficulty-coverage.shs`, which is integrated into the CI gates.

## Integrity

The file begins with a CRC32 checksum header:
```
#sdn-crc32:NNNNNNNNNN
```

After hand-editing, reseal with:
```bash
sh scripts/check/reseal-sdn-crc32.shs doc/08_tracking/bug/bug_db.sdn
```

The checksum is fail-CLOSED: a mismatch makes the entire database load as nil.

## Filing New Bugs

When creating a new bug, include:
1. A title (required)
2. One or more rows in bug_descriptions with details (required)
3. Initial severity (P0-P4)
4. Status (usually "open")
5. A bug_difficulty row (required for non-closed status)

Use a date-based ID when appropriate: `problem_description_YYYY_MM_DD`

## Fix Claims (`fixing`)

Concurrent fixers claim a bug before working on it. Helper: `sh scripts/check/bug-claim.shs`
(wiki page: `doc/07_guide/infra/tracking/bug_fix_claims.md`).

### Main tables
While claimed, the bug's row in both `bugs_active` and `bugs` reads `status=fixing` and
`updated_at` = the claim date. No column is added (bug-gen requires exactly 10 columns, #5738).
`bug-gen` renders a "Fixing (session, since)" section; the typed loader and `check-dbs`
accept `fixing` (the typed `BugStatus` enum maps it to `Investigating`, so any tool that
round-trips a row through that enum writes `investigating` back; re-run `claim` or `reap`).

### bug_fix_claims
`bug_fix_claims |bug_id, state, session_id, claimed_at, heartbeat_at, prev_status, note|`
- **state**: `fixing` | `waiting_verify` | `released` | `done` (done means it landed; the PR number is in note)
- **session_id**: short session/lane id, for example `a6dffc9c/p0f-1`
- **claimed_at / heartbeat_at**: ISO 8601 UTC, for example `2026-11-02T05:40:00Z`
- **prev_status**: main-table status before the claim (restored on release/reap)
- **note**: quoted free text (`PR #N` for done, `abandoned (reaped)` for reaped)
- Multiple rows per bug are allowed (history is kept). Holder rule, identical in the script and bug-gen: the earliest `fixing` row with `claimed_at` strictly after the newest non-fixing row; with none, the newest row is the current state. A stale takeover first appends a `released` (session `takeover`) row.
- A `waiting_verify` row is an ownership handoff event: `session_id` identifies who submitted it, `claimed_at`/`heartbeat_at` record the transition time, and `note` names the required verification. The prior fixing row retains the original start time. It sets main status `fix-implemented-verification-pending` and releases exclusive ownership.
- The writer lock records its shell PID; it is never evicted automatically by age or an observed dead PID. Recovery requires all writers to be stopped before manual lock removal. `BUG_CLAIM_LOCK_RETRIES` controls bounded retry attempts (default 60; 0 is useful for lock-contention fixtures).
- A `fixing` claim with `max(claimed_at, heartbeat_at)` older than 24 h is STALE: it may be
  taken over, and `reap` reverts it. Closed bugs need no claim.

### Commands
| Command | Effect |
|---------|--------|
| `claim <bug_id> <session_id> [note]` | status=fixing + claim row; exit 3 if another live session holds it; exit 4 if closed/unknown |
| `wait-verify <bug_id> <session_id> <required-check>` | Holder-only transition to `fix-implemented-verification-pending`, records owner/check/time in a `waiting_verify` row |
| `check <bug_id>` | Read-only validation of fixing/pending owner and timestamp links; exit 1 when required details are missing |
| `environment <bug_id> <found-env> <repro-env> <unknown\|candidate\|verified> <evidence>` | Append observed/candidate environment metadata to `bug_environments`; found or verified environments require evidence; missing labels remain unknown |
| `heartbeat <bug_id> <session_id>` | refresh `heartbeat_at` (call at least every 2 h) |
| `release <bug_id> <session_id>` | state=released, status back to `prev_status` |
| `done <bug_id> <session_id> <pr>` | state=done, status=`fixed`, note `PR #<pr>` |
| `status <bug_id>` | claim state, session, times, `live`/`STALE` |
| `list-active` | all bugs whose newest claim is `fixing` |
| `reap [--max-age 24h] [--report]` | revert abandoned `fixing` bugs (no claim row, or stale) to `prev_status` and append a `released` row; `--report` is read-only (wired into `must_check_gates.sdn` as a non-blocking report) |
| `show <bug_id> --intent for_fixing --session <id> [--note n]` | print details and atomically claim |
| `show <bug_id> --intent not_for_fixing` | print details, change nothing; `--intent` is required |

Claims are race-checked: after writing, the script re-reads the table; if two live
claims raced, the earlier `claimed_at` wins and the later one backs out (exit 3).
Every write reseals the CRC (`scripts/check/reseal-sdn-crc32.shs`). Exit codes: 0 ok,
2 usage, 3 refused, 4 not claimable. There is no other bug-lookup entry point
(`bug-add`/`bug-gen`/`bug-resolve` only write); `bug-claim.shs show` is the lookup.
