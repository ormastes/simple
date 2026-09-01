# SCV Mission-Critical Allocation (MCI-v2) — status and wiring plan

**Date:** 2026-08-25. Scope: bring `src/lib/scv/**` under the MCI-v2
bounded/domain-arena allocation contract and the `critical` strictness tier.

## Bounded now

`src/lib/scv/alloc_bounds.spl` charges every request through the existing
`DomainArenaV1` facade (`src/lib/nogc_sync_mut/mission_critical/domain_arena_v1.spl`)
— checkpoint → `try_allocate` → commit; Exhausted ⇒ named fail-closed error,
store untouched. No parallel allocator was invented.

| Bound constant | Value | Enforced at |
|---|---|---|
| `SCV_MAX_OBJECT_BYTES` | 268435456 (256 MiB) | `pack.spl scv_pack_import_entry` (raw bytes); `pack_v2.spl scv_pack_resolve_object` (declared entry/delta sizes, before copying) |
| `SCV_MAX_TREE_ENTRIES` | 1000000 | `pack.spl scv_pack_import_entry` (tree line count) |
| `SCV_MAX_DELTA_TARGET_BYTES` | 268435456 | `delta.spl scv_delta_decode` (declared target size, before reconstruction) |
| `SCV_MAX_PARSER_INPUT_BYTES` | 67108864 (64 MiB) | `parser.spl scv_parse_file` (`file_size` before read) |

Pre-existing: `SCV_DELTA_MAX_DEPTH = 10` (`delta.spl`), enforced in
`pack_v2.spl` verify/read paths — unchanged, covered by the spec.

Gate: `scripts/check/check-scv-mission-critical.shs` (fail-closed, `--selftest`
fatal, verdict-last-line; `--lint` opts into the per-file
`lint --profile=critical` sweep). Spec:
`test/integration/app/scv_allocation_bounds_spec.spl` (4/4 green). Evidence:
`build/scv-mci-evidence/scv-allocation-evidence.env`
(`mci-allocation-domain-arena-evidence-v1` shape, `artifact_mode=fixture`;
delta from the canonical producer recorded in the artifact).

## Still needs the domain-arena facade

- `store.spl` write paths (chunk/tree/commit writes) and `src/app/scv/main.spl`
  — owned by a parallel lane at time of writing; that lane should route its new
  `checkpoint`/`new-change` growth points through `scv_alloc_charge`.
- A long-lived per-process SCV arena (today each charge is a fresh
  single-generation arena, i.e. per-request quota, not cumulative per-domain
  accounting).
- `@lint_profile(critical)` file headers: unusable on the current seed — see
  `doc/08_tracking/bug/lint_profile_header_unusable_in_product_files_2026-08-25.md`.
  Tier is enforced via the gate's `--profile=critical` CLI flag instead.

## Exact MCI-v2 lane-table wiring step (for the lane that owns sign-mci-v2-lane.shs)

Add a row to the lane table in `scripts/check/sign-mci-v2-lane.shs` with
lane id `scv-allocation`, producer
`scripts/check/check-scv-mission-critical.shs`, artifact
`build/scv-mci-evidence/scv-allocation-evidence.env`, schema
`mci-allocation-domain-arena-evidence-v1`. Before signing, upgrade the
evidence emission to the canonical producer's full row set (source/config
hashes, launcher receipt+signature, validity window) or invoke
`check-mci-v2-allocation.shs` with SCV's spec/impl paths; until then the
artifact stays `release_eligible=false` by construction.
