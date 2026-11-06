# Seed JIT: `.?` / `??` on Option and Result diverge from pure Simple

- **Date**: 2026-11-06
- **Status**: open
- **Area**: compiler_rust (seed JIT / Cranelift lowering)
- **Related**: error_path_27_some_nil_exists_check_red_by_contract_2026-10-31.md (owner decision 2026-11-06:
  "`.?` in the Rust seed interpreter must behave exactly like pure Simple").

## Repro (seed `run`, program with `main`, `SIMPLE_EXECUTION_MODE=jit` vs `interpret`)
| expression | jit | interpret (= pure contract) |
|---|---|---|
| `c ?? 7` with `c: i64? = Some(nil)` | `3` (raw nil sentinel) | `7` (after this lane's fix) |
| `if Err("e").?` | true | false |
| `not Some(0).?` | `true` | `false` |

## Status
Not fixed in work/seed-try-op-parity (interpreter-only lane). Needs the JIT `Coalesce`/`ExistsCheck`/`not` lowering
to decide presence on the Option/Result tag, never on the raw payload word.
