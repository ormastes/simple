# SCV Workstream E: PROD-006 — Spec Summary

**Spec file:** `test/integration/app/scv_delta_pack_spec.spl`
**Coverage targets:** `src/lib/scv/delta.spl` 80%, `src/lib/scv/pack.spl` 80%, `src/lib/scv/maintenance.spl` 70%

## AC-6 Coverage Map

| AC-6 Clause | Test (`it` block) |
|---|---|
| Large edited files compress better than whole-object gzip packs | "delta encoding produces smaller output than full object for similar content" |
| Delta decoding reconstructs original bytes exactly | "delta decoding reconstructs original bytes exactly" |
| Pack v2 write with delta entries | "pack-write-v2 produces a v2 format payload with entry-delta rows" |
| Pack verify catches invalid base references | "pack-verify-v2 catches missing base reference in entry-delta row" |
| Pack verify catches chain depth exceeding limit | "pack-verify-v2 rejects entry-delta with chain_depth exceeding maximum" |
| Pack verify accepts valid chain within limit | "pack-verify-v2 accepts valid entry-delta chain up to depth limit" |
| GC keeps reachable bases even when loose objects pruned | "GC keeps reachable base objects even when loose delta targets are pruned" |
| Pack read resolves delta chain to reconstruct object | "pack-read-object resolves delta chain and reconstructs original content" |

## Key Interfaces Exercised

- `pack-write-v2` CLI command → `scv_pack_write_v2` / `scv_pack_payload_v2`
- `pack-verify-v2` CLI command → `scv_pack_verify_v2` (validates base refs, depth limit ≤ 10)
- `pack-read-object <kind> <id>` CLI command → `scv_pack_read_object` (chain resolution)
- `gc` CLI command → `scv_gc_prune_packs` + `scv_pack_reachable_base_ids`

## Test Strategy

All tests use `process_run("/bin/sh", ["-c", script])` shell scripts, matching the pattern
of `scv_pack_import_spec.spl` and `scv_pack_verify_safety_spec.spl`. Each test:
1. Creates an isolated `mktemp -d` workspace
2. Runs `init` / `snapshot` to build state
3. Exercises the target command
4. Asserts output with `expect(out).to_contain(...)` using built-in matchers only

## Notes

- `entry-delta` chain depth limit is `SCV_DELTA_MAX_DEPTH = 10` (from `delta.spl`)
- Delta compression test uses 200-line repetitive content where one appended line is the only edit; delta pack must be smaller than full-object gzip pack
- Chain-depth rejection test constructs a 11-deep chain (depth 11 > max 10) directly in payload bytes, bypassing the writer, to verify the verifier's enforcement
- GC base-pinning test verifies `pack-verify-v2` still passes after `gc` — meaning the pack containing the base object was not deleted
