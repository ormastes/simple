# Coverage: value-position `match` arm tails and multi-line lambda bodies ran unrecorded (2026-11-14)

**Status:** FIXED in the seed collector by this change (seed rebuild needed to pick it
up). **Area:** `src/compiler_rust/compiler/src/interpreter/expr/control.rs`,
`src/compiler_rust/compiler/src/interpreter_call/block_execution.rs`,
`src/compiler_rust/compiler/src/interpreter/coverage_helpers.rs`.

Supersedes `coverage_expression_position_if_match_unrecorded_2026-11-14.md`, filed on
`fd5f114a19b` (branch of the `enum_constructor_payload.spl` coverage work). Its symptom,
evidence and line list are carried over below; its diagnosis is corrected.

## Symptom (carried over)

`spl-coverage module` could not report 90% lines for a module written in the
tail-`match` style. `_cov_is_recordable` (`src/lib/common/coverage_module_report.spl`)
counts every line that starts with `if ` or `match `, but the header of an `if` /
`match` evaluated for its value was missing from the artifact while statements under it
were present. `src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl`
read 82.2% (190/231); the 41 missed lines were all such headers (34 `match`, 7 `if` /
`if val`): 29, 32, 36, 44, 61, 63, 67, 90, 92, 97, 102, 107, 112, 124, 135, 157, 164,
166, 172, 176, 180, 184, 257, 297, 300, 315, 353, 362, 415, 421, 455, 469, 472, 513,
514, 524, 550, 576, 598, 600, 610.

## Diagnosis

`Expr::If` / `Expr::Match` carry no span, but that is not what lost these lines. A line
that starts with `if ` / `match ` outside a bracket is parsed as a statement
(`Node::If` / `Node::Match`, both spanned). The collector records a statement in
`exec_node`; a line is lost wherever an executor runs a statement without going through
`exec_node`. There were three such places:

1. `exec_block_fn` (`interpreter/block_exec.rs`): the last statement of a function body,
   of a statement-`match` arm and of an `if` branch. Fixed by PR #9041
   (`a6f47dadbc7`). **All 41 lines above are this class** (re-measured below). The
   82.2% was measured with
   `simple-dynlib-20261113/build/cargo-target/release/simple`, a binary dated
   2026-11-13 15:23; #9041 merged 2026-11-14 06:04 and is not in that worktree
   (HEAD `2ee85bcb89a`).
2. `Expr::Match` evaluation (`interpreter/expr/control.rs`, arm loop): the last
   statement of an arm of a value-position `match` (`val r = match v:`,
   `return match v:`) ran through `exec_if_core` /
   `exec_match_core` with no record. Open until this change.
3. The block-closure executors (`exec_block_closure_into`,
   `exec_block_closure_mut_inner` in `interpreter_call/block_execution.rs`): they
   interpret every statement kind themselves, at every nesting depth, so no line of a
   multi-line lambda body (`val f = \x:` + block) was ever recorded -- `val`,
   assignment, `if`, `match`, `for`, `while`, `return` alike. Listed as "still open" in
   the statement-coverage wiki after #9041. Open until this change.

## Fix

`record_node_coverage_lexical` (coverage_helpers.rs) is called for the arm-tail
statement in (2) and at the head of both statement loops in (3). It records the line
under the module that WROTE the statement (`private_call_caller`: the closure's origin
stamp, else the same owner / entry-file fallback as `current_coverage_file`), because a
closure body inherits `CURRENT_EXEC_MODULE` from its invoker: with
`current_coverage_file` a lambda handed to another module's function would have marked
that module's lines as hit. With coverage off each call is one `OnceLock` load, the
same guard `exec_node` already pays per statement.

Nothing is removed from the denominator and no existing record site changed.

## Red -> green

Fixture `test/fixtures/coverage/covexpr_fixture.spl`, case "records arm-tail and
lambda-body lines of value-position if and match" in
`test/02_integration/app/coverage/spl_coverage_module_spec.spl` (pins the exact
recorded line set and the module figure).

| seed | recorded lines of the fixture | `spl-coverage module` | spec |
|---|---|---|---|
| base `6a71372cabc` (has #9041) | 19 22 39 41 52 53 54 58 65 72 76 88 99 107 | 45.1% (14/31) | 9 passed, 1 failed |
| this change | 19 21 22 28 39 41 42 47 52 53 54 58 65 72 76 77 78 79 80 88 89 91 99 107 108 110 | 83.8% (26/31) | 10 passed |

The five lines still missed are the ones `main()` never reaches: an untaken `else`
(25, 83), an untaken arm's `if` header (32), an untaken arm (94), an uncalled lambda's
body (100). A hit header does not mark them.

`covexpr_cross` hands its lambda to `covexpr_helper.spl`. With the first draft of this
fix (arm tail recorded through `current_coverage_file`) line 110 of the fixture landed
in the 7-line helper as `covexpr_helper.spl, 110`; the spec pins the helper's recorded
lines to its own two (5, 6).

## `enum_constructor_payload.spl` re-measured

Sources of `/home/yoon/dev/simple-letpayload-20261114` at `d013c487322`, the nine
`SIMPLE_COVERAGE=1` artifacts of the original record (`let_annotated_optional_join`,
`enum_payload_type_evidence`, `enum_payload_local_evidence`, `contextual_enum_payload`,
`nil_singleton_type_pipeline`, `optional_enum_payload_owner`,
`enum_payload_inferred_carrier`, `enum_payload_value_shapes`,
`nested_optional_text_nil_pattern`), each recorded with `<seed> run <spec>` and scored
with `spl-coverage module --file <9 artifacts>`:

| seed | lines | missed |
|---|---|---|
| `simple-dynlib-20261113` (pre-#9041), original record | 82.2% (190/231) | the 41 headers |
| same seed, re-recorded here | 82.2% (190/231), `source=unverified` | the 41 headers |
| base `6a71372cabc` (has #9041) | 100.0% (231/231) | none |
| this change | 100.0% (231/231) | none |

So this module was not short of 90% on a current seed: #9041 already records all 41
lines, and the original figure came from a stale seed (its artifacts carry no
`sources |file, crc32|` table, which #9041 added). Decisions are 87.6% (71/81) on base
and on this change.

What this change adds, over the same nine runs (base -> this change): 22,016 -> 22,083
recorded `(file, line)` rows, **0 lost**, 67 gained. Six are arm tails of
value-position `match`es in four compiler modules -- `expression_core.spl` 1126, 1178,
1335 (252 -> 255 of 622), `provider_metadata.spl` 449 (585 -> 586 of 1126),
`switch_operators_calls.spl` 4971, `mir_lowering_stmts.spl` 3787 -- and 61 are
statements of `it` bodies in the test files (block closures).

## Interpreter cost

`<seed> run test/01_unit/compiler/mir/enum_payload_local_evidence_spec.spl` from
`simple-letpayload-20261114` (`d013c487322`), three runs per cell, interleaved
base/fixed and coverage off/on, each capped at 6G. Seeds:
`build/seed-base/simple` (55,067,296 bytes, built from `6a71372cabc`) and
`build/seed-final/simple` (55,072,656 bytes, this change; byte-identical to
`build/cargo-target/release/simple`). Median elapsed / user seconds:

| seed | coverage off | `SIMPLE_COVERAGE=1` |
|---|---|---|
| base | 18.25 / 12.77 | 18.83 / 14.44 |
| this change | 18.77 / 13.47 | 19.86 / 13.76 |

Host under load (a bootstrap run near the memory cap): base coverage-off elapsed
alone spans 15.81-20.28 s, so the +0.5 s coverage-off difference is inside the
noise. The only new work with coverage off is one `is_coverage_enabled()`
`OnceLock` load per block-closure statement and per value-`match` arm tail.

## Not fixed here

- **`Expr::If` / `Expr::Match` have no span.** An `if` / `match` used as a call
  argument or a field initializer is recorded through its enclosing statement's line
  (`val r = f(if c: a else: b)` records the `val`). When it starts its own line inside
  brackets it is a continuation line: not recorded, and not in the denominator either
  (`_cov_scan` skips lines at bracket depth > 0), so no figure depends on it. Recording
  it needs a span on both variants (about 70 pattern sites in the seed). A bare
  expression statement (`f(if c: a else: b)`) is not recorded and not counted.
- **Hits inside a closure body are filed under the invoker's module** for the
  `exec_node` records and for decision rows:
  `coverage_closure_body_hits_filed_under_invoker_2026-11-14.md`.
- Carried over from the original record, not investigated: a function `val keep = 1` /
  `if val y = x:` (whose body ends `case _: ()`) / `keep` returned `()` instead of `1`
  on the seed interpreter for a present `x` that took the wildcard arm.

## Re-verification (2026-11-14, handover)

- Spec `spl_coverage_module_spec.spl` re-run on each seed (`bin/simple` pointed at it):
  `seed-base` 9 passed / 1 failed (the new case); `seed-final` 10 passed, 0 failed.
- Nine-artifact score re-run with `seed-final`: `build/cov9/old_run` (dynlib seed,
  pre-#9041) 82.2% (190/231) `source=unverified`; `build/cov9/base_run` 100.0%
  (231/231); `build/cov9/final_run` 100.0% (231/231). Lines still missed: none.
- `cargo test --release -p simple-compiler --test interpreter_coverage_line`: 20 passed.
- Neighbouring coverage specs, base and this change identical:
  `coverage_unary_not_probe_spec` ERROR 0/3 under `test` on both seeds (3/3 under
  `run` on both), `test_runner_coverage_decisions_extraction_spec` 2 skipped on both;
  `spl_coverage_cli`, `coverage_module_report`, `coverage_runtime_ffi`,
  `spl_coverage_log_modes`, `coverage_aspect_pack` pass. Pre-existing, not caused here.
