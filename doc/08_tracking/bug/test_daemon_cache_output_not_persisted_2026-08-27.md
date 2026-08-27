# test_daemon cache spec RED: result_output field gone, output not persisted across save/load

- Date: 2026-08-27
- Found via: sspec modernization residual batch resid6_part_00.

## Evidence

`test/01_unit/app/test_daemon/test_daemon_cache_module_spec.spl` fails at HEAD
(verified on a clean `git checkout HEAD --` copy):

- `bin/simple test` -> `Results: 1 total, 0 passed, 1 failed`
- `bin/simple run` detail: `semantic: class 'TestCacheEntry' has no field named
  'result_output'`

Root cause: `TestCacheEntry` (src/app/test_cache_shared.spl:19) names the field
`output` (renamed from `result_output`). Additionally the persisted line format
(src/app/test_cache_shared.spl:93) does not include the output column and
`shared_cache_load_entries` restores `output: ""` (line 118), so the spec's
oracle — cached output text surviving save/load — cannot be satisfied by the
current implementation even after the field rename.

## Disposition

Left RED per testing rules (a correct spec that fails documents a real defect).
Unblock: either persist output in the cache line format/restore it on load, or
deliberately drop the output-persistence oracle and record that decision.

Scoring note: the spec's SSDoc score was also capped by ORA-002 because its
fixture string embeds `expect(1).to_equal(1)`, which the line-based scorer
misreads as a local-arithmetic oracle. Once the RED is resolved, wrapping the
fixture text differently lifts the false blocker (verified experimentally:
score 94 with the fixture respelled).
