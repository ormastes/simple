# Feature Request Entry Template

Copy this block under `## Open Requests` in the target tracker (e.g.
`nvfs_requests.md`). Assign the next free id in the `FR-<TARGET>-####` series.

```markdown
### FR-NVFS-0000 — <short title>

- **Filed-on:** YYYY-MM-DD
- **Filed-by:** <author / agent / session>
- **Target:** nvfs  (or: <other storage/runtime target>)
- **Priority:** P0 | P1 | P2
- **Status:** Open | Accepted | Implemented | Rejected
- **Requested-semantics:**
  <one short paragraph — the behavior/API you need, with a code-shape hint
   if relevant; do NOT paste a full design here, link instead>
- **Acceptance-criteria:**
  - [ ] <observable condition 1>
  - [ ] <observable condition 2>
- **Related-upfront:** <e.g. `doc/05_design/nvfs/from_spostgre.md §S3`, or `none`>
- **Related-design-doc:** <e.g. `doc/05_design/nvfs_design.md §4.1`, or `tbd`>
- **Related-issue:** <github issue URL, or `none`>
- **Notes:** <optional — blockers, alternatives considered, crash log refs>
```

## Id scheme

- `FR-NVFS-####` — requests targeting NVFS (the NVMe-aware filesystem).
- `FR-STORAGE-####` — requests targeting the shared `src/lib/nogc_sync_mut/storage/`
  trait surface (cross-cutting between spostgre / svllm / nvfs).
- Monotonic per target; do not reuse ids even after a `Rejected`.

## Lifecycle

`Open` → `Accepted` (triage decision recorded) → `Implemented` (link design-doc
or issue that closes it) or `Rejected` (one-line reason).

An entry may not move to `Implemented` without a `Related-design-doc` or
`Related-issue` link — this keeps the tracker honest against silent drops.

## Minimum viable entry

Everything above is required EXCEPT `Related-issue` and `Notes`. If the request
is discovered without a matching upfront item, set `Related-upfront: none` and
explain the gap in `Notes`.
