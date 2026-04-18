# NVFS Feature Requests

Secondary channel for feature requests against the NVFS (SimpleFS-NV)
filesystem. See `README.md` for the primary vs secondary channel rule.

- **Target:** nvfs
- **Owning design doc:** `doc/05_design/nvfs_design.md`
- **Upfront contributions (primary channel):**
  - `doc/05_design/nvfs/from_spostgre.md`
  - `doc/05_design/nvfs/svllm_requirements.md`

## Schema

Entries use the fields in `TEMPLATE.md`:

| Field | Notes |
|-------|-------|
| id | `FR-NVFS-####`, monotonic |
| title | verb-led, ≤ 80 chars |
| Filed-on | `YYYY-MM-DD` |
| Filed-by | author / agent / session id |
| Priority | `P0` / `P1` / `P2` (required at `Accepted`) |
| Status | `Open` / `Accepted` / `Implemented` / `Rejected` |
| Requested-semantics | one-paragraph description |
| Acceptance-criteria | observable bullets |
| Related-upfront | `from_spostgre.md §S#`, `svllm_requirements.md §R#`, or `none` |
| Related-design-doc | `nvfs_design.md §#`, or `tbd` |
| Related-issue | GH issue URL (optional) |

An entry may not move to `Implemented` without a `Related-design-doc` or
`Related-issue` link.

## Upfront Contributions (primary channel — do not re-file here)

Listed here for cross-reference **only**. The upfront doc
`doc/05_design/nvfs/from_spostgre.md` is the source of truth for these items —
edits go there, not in this tracker.

| Ref | Title | Priority | Source |
|-----|-------|----------|--------|
| `[UPFRONT] S1` | `arena_create` per storage class | P0 | `from_spostgre.md §S1` |
| `[UPFRONT] S2` | `arena_append_aligned` | P0 | `from_spostgre.md §S2` |
| `[UPFRONT] S3` | `arena_seal` + `arena_discard` with generation pinning | P0 | `from_spostgre.md §S3` |
| `[UPFRONT] S4` | `arena_clone_range` for page-version cloning | P0 | `from_spostgre.md §S4` |
| `[UPFRONT] S5` | Preferred I/O granule + capability query (`fs_caps`) | P0 | `from_spostgre.md §S5` |
| `[UPFRONT] S6` | Capability-gated atomic-pointer-record publish | P0 | `from_spostgre.md §S6` |
| `[UPFRONT] S7` | NVMe Flush / FUA pass-through tied to durability classes | P0 | `from_spostgre.md §S7` |

The seven `[UPFRONT]` items above are **not** open entries. They are already
locked into the fs-API contract. Do not re-file them here. Updates to their
wording/semantics belong in `from_spostgre.md` (and mirror into
`nvfs_design.md`).

Six P1 stretch items (`S-stretch-1..6` — ZNS zone-append, FDP PIDs,
namespace-per-class, copy offload, CMB/PMR, DSM trim) also live in
`from_spostgre.md`; they are intentionally omitted from the table above to
keep the `[UPFRONT]` list focused on the load-bearing seven.

## Open Requests

_No entries yet._

Entries here are filed during Phase 5+ implementation (per SStack state file
`.sstack/spostgre-nvfs-storage/state.md`) when an NVFS need is discovered that
is not already covered by the `[UPFRONT]` items above. Use `TEMPLATE.md` and
append under this heading.

## Closed (Implemented or Rejected)

_No entries yet._

Closed entries are moved here from `## Open Requests` (never deleted) with
`Status: Implemented` or `Status: Rejected` and the required link/reason.
