# MIR specs through `parse_full_frontend` lower zero functions on a fresh-seed worktree lane

**Status:** OPEN (observed 2026-11-12, aarch64, Linux)
**Area:** test harness / seed interpreter

## Symptom

Running `parse_full_frontend` → `HirLowering.lower_module` → `MirLowering.lower_module`
specs with the fresh Rust seed (`src/compiler_rust/target/bootstrap/simple`
built from `75039781798` in the pinned bootstrap snapshot) from the worktree
`/home/yoon/dev/simple-boot-fable-fix-20261112`, every example that inspects
`mir.functions` sees an empty module while both lowerings report **zero errors**:

| spec | result |
|---|---|
| `test/01_unit/compiler/mir/text_codepoint_panic_abi_spec.spl` | `Results: 2 total, 0 passed, 2 failed` (`expected 0 to equal 1` — no `rt_panic` call found) |
| `test/01_unit/compiler/mir/array_insert_native_lowering_spec.spl` | `Results: 6 total, 1 passed, 5 failed` |
| new probe spec (p2_add-shaped fixture, deleted before commit) | `diag:functions=0,calls=0,hir_errors=0,mir_errors=0,keys=0,hir_fns=0` |

Command shape: `SIMPLE_BOOTSTRAP=1 SIMPLE_RUST_SEED_WARNING=0 <seed> test <spec> --no-session-daemon`.

## Why it matters

357 specs under `test/01_unit/compiler/mir/` use `parse_full_frontend`. If the
same happens under the Stage 2 compiler-test matrix
(`repository_test_execution=interpreter`), those rows fail for a reason that
has nothing to do with the compiler change under test, and a real
regression spec (e.g. one for the runtime-callee-origin fix `a29ebd56af4`)
cannot be validated on the lane.

## Unanswered

- Whether `parse_full_frontend` returns an empty item list (`parsed.items.len()`)
  or HIR lowering drops the functions — the diagnostic run that would have
  printed `items=` did not surface the assertion line (log noise), and the
  lane moved on. Rerun the probe with `print(...)` inside the `it` body.
- Whether the same specs pass on the deployed `bin/simple` of the main checkout
  (no `bin/simple` existed there during the observation).

## Evidence

- Lane: `/home/yoon/dev/simple-boot-fable-20261112` (runs `build/bootstrap-fable-{1..6}`), fix branch `work/boot-fable-fix-20261112`.
- Logs: scratchpad `origin_green*.log`, `ref_spec.log`, `ref2.log` (session-local).
