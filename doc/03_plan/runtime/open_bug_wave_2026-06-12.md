# Open Bug Wave — Plan & Status (2026-06-12)

Follow-on to `remaining_hardening_tasks_2026-06-11.md` (S1–S10, closed).
Scope: all remaining open seed/interpreter bugs, fixed by parallel agents,
verified fresh by the orchestrator, committed path-scoped, pushed often.

## Status table

| ID | Bug | Fix | Status |
|----|-----|-----|--------|
| A5 | selfhosted MCP binary segfault | stale doc — binary healthy | DONE, pushed `c0c95b026b` |
| A6 | html_compat fixture18 timeout | stale doc — spec passes at real path `test/03_system/gui/wm_compare/html_compat_spec.spl` | DONE, pushed `80bc7dc91c` |
| A2 | FAT32 dirent write-back | `FileHandle.dirent_sector/offset` + `_update_dirent()` patches cluster hi/lo + size; new `fat32_dirent_spec.spl` 7/7 | DONE, pushed `a734541c33` |
| A1 | static-method default params unreachable | `constructor_overload_score` now scores `required<=provided<=total`; +5 tests | DONE, pushed `be08dc3ccc` |
| A4 | compiled array OOB read segfault | root cause: `compile_inline_array_get/set` deref before nil/tag check; code fix rides parallel parser track local commit `adc8dcad379` | doc pushed `18e5fb2033`; code lands when parser track pushes |
| B3 | generator `yield` crash (exit 132) | `async_ops.rs` trap→NIL return safety net; +2 MIR-lower regression tests (async_desugar 7/7 green) | DONE, on main via resolution-commit sweep (`62f9ce296dc` lineage); probe exit 0 |
| A3 | positional class match wide destructure | `pattern_matches` gains `classes` param + `Pattern::Enum`-over-`Value::Object` branch; 6 call sites in `interpreter_control.rs`; +5 tests (5/5 green) | DONE, pushed `66b65e11719` (interpreter mode; cranelift open) |

## Wave closed 2026-06-12

All steps completed: tests verified fresh (interpreter_patterns 5/5,
async_desugar 7/7), probes green (B3 exit 0, A3 `matched: 10 20 30` under
`SIMPLE_EXECUTION_MODE=interpreter`, A1 prints 5/7), all fixes on main,
seed redeployed to `bin/release/x86_64-unknown-linux-gnu/simple_seed`
(backup `simple_seed.bak.2026-06-12-preA3B3`) and smoke-gated:
probes + `math_spec.spl` 13/13 via stage4 `bin/simple test` delegation.
Note: test/ was reorganized to numbered dirs mid-wave; old spec paths like
`test/01_unit/lib/std/*` are gone — runner reports plain FAILED (not
file-not-found) for missing paths.

## Open follow-ups (not in this wave)

- **B3 cranelift for-in gap**: `for x in gen()` still exits 139 in compiled mode
  (documented in async bug doc line ~86). Needs generator state-machine support
  in the cranelift path, not a safety net.
- **A3 cranelift**: positional class match fixed in interpreter only; compiled
  path still open (bug doc tracks it).
- **A4 code fix**: lands with parser track's push of `adc8dcad379` (calls.rs ±104).
- **B5 eager-async**: DOCUMENTED-CANONICAL, pinned by 7 `test_b5_*` tests
  (`31fe3a3bede`); no production change planned.
- **FINDING-T2-dirent**: Optional-unwrap interpreter limitation forced sentinel
  `-1` returns in FAT32 `_find_root_entry`; revisit when Optional unwrap works
  in interpreter element contexts.
- **Parser completion** (foreign track): lean-parser language coverage, weeks-scale,
  own plan — do not touch its files (`codegen/**`, `mir/lower/**`, `Cargo.toml`, etc.).
