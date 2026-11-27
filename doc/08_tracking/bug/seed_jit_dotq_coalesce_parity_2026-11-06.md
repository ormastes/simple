# Seed JIT: `.?` / `??` on Option and Result diverge from pure Simple

- **Date**: 2026-11-06
- **Status**: fix-implemented-verification-pending (work/interp-p2-dotq)
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

## Fix (work/interp-p2-dotq, 2026-11-06)
- `hir/lower/expr/control.rs` `lower_coalesce`: tagged-slot presence is now `rt_is_some(s) and rt_is_some(rt_unwrap_or_self(s))`,
  so `Some(nil) ?? d` / `Ok(nil) ?? d` take the default (was the raw sentinel `3`).
- `runtime/src/value/objects.rs` `rt_is_present`: `Result::Err` is absent, so `if Err(e).?:` is not taken and value-position
  `Err(e).?` is nil (was the Err payload word).
- `hir/lower/expr/operators.rs` `lower_unary`: `not x.?` negates presence (lowers the operand via `lower_condition`).
- Parity spec: `test/01_unit/compiler/interpreter/dotq_jit_interp_parity_spec.spl` (+ probe `probe_dotq_jit_parity.spl`)
  runs the same probe on `SIMPLE_EXECUTION_MODE=jit` and `=interpreter` and asserts the pure-Simple contract values.
- Verification pending a seed redeploy: deployed `bin/simple.exe` predates the fix; verified on a test-only seed build
  (`CARGO_TARGET_DIR=C:/dev/wt/_ip2d_target cargo build --release --bin simple`, then
  `SIMPLE_TEST_BINARY=<that exe> bin/simple.exe test test/01_unit/compiler/interpreter/dotq_jit_interp_parity_spec.spl`).

## Residual (not in this row's repro; pre-existing)
Value-position `.?` on a `Result` under the JIT renders a raw word: `"{Ok(5).?}"` prints `5248785692033`, `"{Err(e).?}"`
prints `3` (both engines-before and after this fix; interpreter prints `5` / `nil`). Cause: `rt_unwrap_or_self`
deliberately unwraps only `Option` (objects.rs:530), while `lower_exists_check` types the result as the Result payload.
Needs a Result-aware unwrap builtin wired into MIR's name+type unboxing (lowering_expr_builtin.rs:310). Kept out of the
parity probe until then.
