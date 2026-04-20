# Feature Request Tracker

Unified tracker for feature requests filed against storage/runtime targets that
have their own source-of-truth design docs — primarily NVFS today, extensible
to other targets as they come online.

## Purpose

Capture concrete, trackable asks discovered during implementation work against
an upstream/side module, so the owning design track can reconcile them without
relying on bug reports or lossy Slack-style chatter.

## Primary vs secondary channel

Per memory note `feedback_svllm_drives_nvfs_design.md` (2026) the convention
used across this project is:

- **Primary channel — upfront design contributions.** Upstream consumers
  (spostgre, svllm, ...) produce design-doc contributions alongside their own
  design work. For NVFS, these live under `doc/05_design/nvfs/`:
  - `doc/05_design/nvfs/from_spostgre.md` — spostgre's upfront contribution
    (§S1..S7 + §S-stretch-1..6).
  - `doc/05_design/nvfs/svllm_requirements.md` — svllm's upfront contribution
    (§R1..R9).
  The owning design doc (`doc/05_design/nvfs_design.md`) reconciles both in a
  single pass. Items listed there are **not** re-filed in this tracker.
- **Secondary channel — this tracker.** Requests discovered during Phase 5+
  implementation that were not anticipated by the upfront contributions. These
  are filed here as `FR-NVFS-####` entries and must reference which upfront
  section (if any) they extend.

If you are tempted to file something here that is already covered upfront,
reference the upfront section instead. Duplicate entries add noise without
adding information.

## Files

| File | Purpose |
|------|---------|
| `README.md` | This file. |
| `TEMPLATE.md` | Single-entry template. Copy into a target's file. |
| `nvfs_requests.md` | NVFS-targeted requests (secondary channel for NVFS). |
| `simpleos_os_requests.md` | SimpleOS scheduler, process lifecycle, and SOSIX sharing requests. |

Additional target files (e.g. `storage_requests.md`) follow the same layout:
header → schema → `## Upfront Contributions` (cross-ref) → `## Open Requests`.

## How to file

1. Pick the target file (e.g. `nvfs_requests.md`). Create it if the target does
   not yet have one; mirror `nvfs_requests.md`'s structure.
2. Copy the block from `TEMPLATE.md` under `## Open Requests`.
3. Assign the next free id (`FR-<TARGET>-####`, monotonic, no re-use).
4. Fill in `Requested-semantics`, `Acceptance-criteria`, `Related-upfront`,
   `Related-design-doc`. The last two may be `none`/`tbd` at intake; the entry
   may not close without them populated.
5. Leave `Status: Open` at intake. A later triage pass moves it to `Accepted`,
   `Implemented`, or `Rejected`.

## Lifecycle

```
Open ── (triage) ──► Accepted ── (design updated / PR merged) ──► Implemented
  │                                                             ▲
  └── (triage, with reason) ──► Rejected                         │
                                                                 │
                            Implemented requires a non-empty ────┘
                            Related-design-doc OR Related-issue.
```

- `Open` — default at intake.
- `Accepted` — owning track has agreed to act; `Priority` must be set.
- `Implemented` — the design doc or a merged PR now covers the request; link it
  in `Related-design-doc` or `Related-issue` before flipping state.
- `Rejected` — one-line reason required in `Notes` (duplicate, out-of-scope,
  superseded-by-upfront, etc.).

Entries are append-only: never delete an entry; change its `Status` instead.

## Schema

Every entry uses the fields in `TEMPLATE.md`:

| Field | Required | Notes |
|-------|----------|-------|
| id | yes | `FR-<TARGET>-####` |
| title | yes | ≤ 80 chars, verb-led |
| Filed-on | yes | `YYYY-MM-DD` |
| Filed-by | yes | author / agent / session id |
| Target | yes | `nvfs`, `storage`, ... |
| Priority | yes once Accepted | `P0` / `P1` / `P2` |
| Status | yes | `Open` / `Accepted` / `Implemented` / `Rejected` |
| Requested-semantics | yes | one paragraph |
| Acceptance-criteria | yes | bulleted, observable |
| Related-upfront | yes | upfront doc §section, or `none` |
| Related-design-doc | yes to close | design doc §section, or `tbd` |
| Related-issue | no | GH issue URL |
| Notes | no | blockers / alternatives / crash refs |

## Cross-references

- Upfront (primary) channel:
  - `doc/05_design/nvfs/from_spostgre.md`
  - `doc/05_design/nvfs/svllm_requirements.md`
- Owning design docs:
  - `doc/05_design/nvfs_design.md`
  - `doc/05_design/spostgre_design.md`
- Related trackers under `doc/08_tracking/`:
  - `bug/` — defect tracking
  - `todo/` — code-level TODO scan output
  - `task/` — task tracking
- Scope and channel rationale: memory note
  `feedback_svllm_drives_nvfs_design.md` (in the session author's
  `~/.claude/projects/.../memory/` index).

## Non-goals

- **Not a bug tracker.** Defects go under `doc/08_tracking/bug/`.
- **Not a design venue.** Long design discussion belongs in the owning design
  doc under `doc/05_design/<target>/`; link back from the FR entry.
- **Not a queue for upfront items.** If you are an upfront consumer, put your
  requirement in the upfront contribution doc, not here.
