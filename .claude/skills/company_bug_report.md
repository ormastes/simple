---
name: company_bug_report
description: Daily company bug-report dispatcher — ingest engineering email, fetch FW/dump/notes via MinIO, extract Jira keys, route to mail/bug_review/itf. Routes to sub-skills.
---

# Company Bug Report Skill — Dispatcher

End-of-day pipeline that turns the day's bug-report inbox into a per-bug
markdown digest under `doc/08_tracking/debug/YYYY-MM-DD.md`. The dispatcher
itself only routes; the heavy lifting lives in `spipe_loop --daily-debug`
(orchestrated cycle) and the `bin/itf daily-debug` driver
(`src/app/itf/cmd_daily_debug.spl`).

## Usage

```
/company_bug_report <command> [args]
```

## Commands

| Command | Example | Description |
|---------|---------|-------------|
| `ingest` | `/company_bug_report ingest` | Run the full daily cycle (delegates to `/spipe_loop --daily-debug`) |
| `fw <ticket>` | `/company_bug_report fw ABC-123` | Download firmware artifacts only via `itf minio get` |
| `dump <ticket>` | `/company_bug_report dump ABC-123` | Download crash dumps only via `itf minio get` |
| `notes <ticket>` | `/company_bug_report notes ABC-123` | Fetch engineering notes only |
| `find-key <ticket>` | `/company_bug_report find-key ABC-123` | Extract severity, owner, target SoC from ticket text |
| `report [date]` | `/company_bug_report report 2026-04-26` | Print path of the daily digest for a given day (default: today) |

## Dispatch Logic

### Parse

Split `args` into `command` and `rest`. If `command` is empty, print the
commands table and exit 0.

### Route

**`ingest`:**
Invoke `/spipe_loop --daily-debug` (forward any flags such as `--quiet`,
`--dry-run`). The loop in turn calls `bin/itf daily-debug` with the same
flags so the CLI driver does the actual I/O.

**`fw <ticket>`:**
1. `bin/itf jira view <ticket> --json` to discover MinIO URLs in the body.
2. Filter URLs whose path ends in `.bin`, `.elf`, `.hex` (firmware classifier
   from `cmd_daily_debug.spl::triage_kind`).
3. For each: `bin/itf minio get <url> -o build/debug/<ticket>/fw/<basename>`.

**`dump <ticket>`:**
Same flow as `fw`, but filter `.dmp`, `.core`, `.crash` and store under
`build/debug/<ticket>/dump/`.

**`notes <ticket>`:**
Same flow, filter `.log`, `.txt`, `.md`, store under `build/debug/<ticket>/notes/`.
Also `bin/itf jira view <ticket>` to dump the issue body to
`build/debug/<ticket>/notes/<ticket>-jira.md`.

**`find-key <ticket>`:**
1. `bin/itf jira view <ticket> --json`.
2. Run the heuristic extractor (regex-based, mirroring the body-parser used
   by `cmd_daily_debug.spl`):
   - `Severity:\s*(S[0-4]|Critical|High|Medium|Low)`
   - `Owner:\s*([\w\.\-@]+)`
   - `Target SoC:\s*([\w\-]+)` / `SoC:\s*([\w\-]+)` / `Platform:\s*([\w\-]+)`
3. Print `severity`, `owner`, `target_soc` as a 3-row key:value table.

**`report [date]`:**
Resolve `date` (default today, ISO `YYYY-MM-DD`). Print the absolute path of
`doc/08_tracking/debug/<date>.md`. If missing, exit 1 with a hint to run
`/company_bug_report ingest` first.

## Prerequisite Checks

Before any non-`report` command:
- `bin/mail auth status` — Outlook IMAP/Graph configured (needed for `ingest`).
- `bin/itf jira auth status` — Jira read access (needed for `fw`/`dump`/`notes`/`find-key`).
- `bin/itf minio status` — MinIO endpoint + credentials reachable.
- Configs expected:
  - `~/.config/itf/config.sdn` (jira.url, minio.endpoint, minio.bucket)
  - `~/.config/itf/auth.sdn` (jira.token, minio.access_key, minio.secret_key)
  - `~/.config/itf/spipe_daily.sdn` (auto-managed watermark, mode 0600)

If any check fails, redirect to `/repo_and_pull_req setup jira`,
`/mail setup`, or print the missing section of `~/.config/itf/config.sdn`
and exit 1.

## Integration

| Skill | When Used |
|-------|-----------|
| `/spipe_loop --daily-debug` | `ingest` delegates the 7-step pipeline |
| `/mail` | `ingest` reads Outlook inbox via the mail adapter |
| `/bug_review` | Triaged bugs surface as `bug_review` items in the digest |
| `/repo_and_pull_req` | Jira issue lookups (`jira view`, read-only) |

## Notes

- Q3 default: this skill is the *only* place Jira is used as an active
  ticket-info source. The L2/L3 PR-review path still skips Jira per project
  default.
- All writes to `doc/08_tracking/debug/` go through the driver; the
  dispatcher itself never writes files.
- TODO: cross-link the arch doc once Agent A lands
  `doc/05_design/spipe_infra_arch.md`.
