# SCV specs fail on test-runner interpreter: `file_rename` recursion depth 1000

- Date: 2026-08-26
- Found via: sspec wave-2 dual check (batch D), `/tmp/sspec_census/w2_03`
- Specs affected: `test/integration/app/scv_forced_unparsed_spec.spl` (all 6 scenarios), sibling `test/integration/app/scv_commit_parse_policy_spec.spl` fails identically.
- Wider red set (same lane, verified 2026-08-26 by wave-2 batch C, all scoring >80 with assertions untouched):
  `scv_generic_cst_spec.spl` (1/4 fail), `scv_metadata_db_spec.spl` (5/5 fail), `scv_nvim_protocol_spec.spl` (5/7 fail), `scv_parser_lock_spec.spl` (5/5 fail), `scv_query_packs_spec.spl` (1/5 fail), `scv_symbol_entity_spec.spl` (2/3 fail). All part of the in-flight SCV migration WIP.

## Symptom
`bin/simple test test/integration/app/scv_forced_unparsed_spec.spl` — every scenario dies with:
```
stack overflow: recursion depth 1000 exceeded in function 'file_rename'
```

## Analysis
- Not an oracle defect: on the `bin/simple run` JIT path the same API calls produce exactly
  what the spec asserts (`policy: forced_unparsed`, `mode: line`, `public_ready: blocked`,
  audit rows, `blocks=true`).
- Fails only on the interpreter test-runner path.
- `src/lib/scv/` is uncommitted WIP from another session; whole lane currently red.
- `file_rename` (io_runtime extern) hits interpreter recursion limit.

## Status
Pre-existing lane failure at the time of the sspec modernization pass; assertions left
untouched, spec scores 95 with 0 blockers. Unblock condition: fix/land the `file_rename`
interpreter recursion handling or the owning scv WIP session lands its tree.
