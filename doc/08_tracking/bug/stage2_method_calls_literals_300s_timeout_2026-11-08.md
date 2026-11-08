# method_calls_literals.spl exceeds fixed 300s native file timeout

Severity P2 (perf, first-object-in-10s rule violated).
Status: **fix-implemented-verification-pending** (2026-11-09). Native
verification = a stage2 run without `--timeout` that compiles this file
inside the default 300 s budget.

## Repro (original)

stage2 native-build (`seed.exe native-build --backend llvm --target
x86_64-pc-windows-gnu ...`, no `--timeout`) compiles every file but
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` times out at
300 s (`DEFAULT_NATIVE_FILE_TIMEOUT_SECS`); reproduced twice (stage2 #5, #6),
184 files NOT_ATTEMPTED afterward. Workaround in `run4.ps1`: `--timeout 1500`.

## Diagnosis (2026-11-09, stage2 seed `C:/dev/p3new/stage2new/seed.exe`, warm object cache so only this file recompiles)

| run | threads | file wall | file cpu | process peak WS |
|---|---|---|---|---|
| baseline, release/1.0.0 @ e8e93c66be8 | 8 | 317.8 s | 316.5 s | 2710 MB (whole build) |
| baseline, single file dirty | 1 | 311.0 s | 310.2 s | 1322 MB |
| AFTER split, single file dirty | 8 | **52.1 s** | 51.6 s | 1954 MB (whole build, 285 files) |
| AFTER split, single file dirty | 1 | **42.6 s** | 42.4 s | 1182 MB |

After-split phase split (8-thread run): compile began t=259.2 s, MIR trace
t=270.6 s, object t=311.3 s -> frontend ~11 s, LLVM ~41 s. Same code volume
(3,396 lines -> 1,366 + 1,259 + helpers), 6.1x less time: the cost is
superlinear in *function* size, not file size.

Phase split (single-thread run, `SIMPLE_NATIVE_FILE_TIMING=1` +
`SIMPLE_TRACE_MIR_FUNCTIONS=1`, stderr timestamps): compile of the file
began at t=286.1 s, the MIR-functions trace (emitted after parse + HIR + MIR
lowering) fired at t=301.0 s, the object landed at t=597.1 s. So
**parse+HIR+MIR ~= 15 s; LLVM backend (MIR->LLVM IR + LLVM passes) ~= 296 s**.

Why: the file has 81 methods but one of them, `MirLowering.lower_method_call`,
was a single **3,396-line** body (lines 2554-5949). Per-function cost in the
LLVM lane is superlinear in function size (same class as the lint note in
`.claude/rules/commands.md`: content complexity, not declaration count, is the
driver), so that one function dominated: the next-slowest compiler file
(`10.frontend/core/__init__.spl`) took 101 s.

## Fix (pure Simple, no seed change)

Mechanical split of `lower_method_call` into read-only helpers (every moved
block was verified to read, never write, the outer locals it uses; blocks
that update the `prelowered_method_receiver` memo stayed inline so the
receiver is still lowered exactly once):

- `try_lower_dict_builtin_method_v1`, `try_lower_text_join_v1`,
  `try_lower_text_starts_with_v1`, `try_lower_text_ends_with_v1`,
  `try_lower_text_char_at_v1`, `try_lower_text_search_and_transform_v1`
  (each returns `LocalId?`, nil = not applicable, caller falls through)
- `lower_method_call_by_resolution_v1` (the trailing `match resolution:`
  dispatcher, ~1,250 lines)

Diff is a pure line move (0 removed lines not re-added; 67 new lines are the
call sites, helper signatures and a comment). Largest method is now 1,366
lines (`lower_method_call`), then 1,259 (`lower_method_call_by_resolution_v1`).

## Prevention

`test/01_unit/compiler/50.mir/method_calls_literals_function_size_budget_spec.spl`
pins every method body in the file to <= 1,500 lines and requires the split
helpers to exist. RED on the original (`expected lower_method_call is 3396
lines (budget 1500) to equal within budget`), GREEN after. Regression specs
exercising the moved arms (`dict_method_dispatch_spec`,
`methods_mir_receiver_shapes_spec`, `enum_subject_owner_recovery_spec`) pass
28/28.

Left open: the superlinear term itself lives in the seed's LLVM lane and is
untouched; a follow-up could add a per-function MIR-size warning in the
native builder. Remove `--timeout 1500` from `run4.ps1` once native
verification confirms the file compiles under 300 s.
